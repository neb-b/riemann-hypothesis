module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
public import Formalism.PolynomialDimension.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0781
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0783
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsAffineOpenOfFiniteOpensProj
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderUnipotentModTwoPrimes
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.Neat

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

lemma apply_mem_smul_top (I : Ideal R) (T : Module.End R M) {y : M}
    (hy : y ∈ I • (⊤ : Submodule R M)) : T y ∈ I • (⊤ : Submodule R M) := by
  have h : (I • (⊤ : Submodule R M)).map T ≤ I • (⊤ : Submodule R M) := by
    rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
  exact h ⟨y, hy, rfl⟩

lemma pow_add_sub_pow_mem (I : Ideal R) (A B : Module.End R M)
    (hB : ∀ x, B x ∈ I • (⊤ : Submodule R M)) (n : ℕ) :
    ∀ x, ((A + B) ^ n - A ^ n) x ∈ I • (⊤ : Submodule R M) := by
  induction n with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    have : (A + B) ^ (n + 1) - A ^ (n + 1) = ((A + B) ^ n - A ^ n) * A + (A + B) ^ n * B := by
      rw [pow_succ, pow_succ]; noncomm_ring
    rw [this, LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply]
    exact Submodule.add_mem _ (ih _) (apply_mem_smul_top I _ (hB x))

lemma pow_prime_pow_unipotent (I : Ideal R) (α : Module.End R M) {p : ℕ} (hp : p.Prime)
    (hpI : (p : R) ∈ I) (a r : ℕ) (h : ∀ x, ((α - 1) ^ r) x ∈ I • (⊤ : Submodule R M)) :
    ∀ x, ((α ^ p ^ a - 1) ^ r) x ∈ I • (⊤ : Submodule R M) := by
  obtain ⟨F, hF⟩ := (Commute.one_right (α - 1)).exists_add_pow_prime_pow_eq hp a
  have hγ : α ^ p ^ a - 1 = (α - 1) ^ p ^ a + (p : Module.End R M) * ((α - 1) * (1 * F)) := by
    rw [sub_add_cancel, one_pow] at hF; rw [hF, mul_assoc, mul_assoc]; abel
  have hB : ∀ x, ((p : Module.End R M) * ((α - 1) * (1 * F))) x ∈ I • (⊤ : Submodule R M) := by
    intro x
    rw [Module.End.mul_apply, Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul R]
    exact Submodule.smul_mem_smul hpI trivial
  intro x
  have h1 := pow_add_sub_pow_mem I ((α - 1) ^ p ^ a) _ hB r x
  rw [← hγ, LinearMap.sub_apply] at h1
  have hle : r ≤ p ^ a * r := Nat.le_mul_of_pos_left r (pow_pos hp.pos a)
  have h2 : (((α - 1) ^ p ^ a) ^ r) x ∈ I • (⊤ : Submodule R M) := by
    rw [← pow_mul, ← Nat.add_sub_cancel' hle, pow_add, Module.End.mul_apply]
    exact h _
  have := Submodule.add_mem _ h1 h2
  simpa using this

end GlobalTheory.Neat

namespace GlobalTheory.Neat

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

lemma eq_one_of_unipotent_mod_of_unit [IsDomain R] [IsNoetherianRing R] [Module.Finite R M]
    [Module.IsTorsionFree R M] (I : Ideal R) (hI : I ≠ ⊤) (γ : Module.End R M) (b r : ℕ)
    (hb : γ ^ b = 1) (c : R) (hc : 1 - c * (b : R) ^ (r + 1) ∈ I)
    (h : ∀ x, ((γ - 1) ^ r) x ∈ I • (⊤ : Submodule R M)) : γ = 1 := by
  have hSN : (∑ i ∈ Finset.range b, γ ^ i) * (γ - 1) = 0 := by
    rw [geom_sum_mul, hb, sub_self]
  have hE : (b : Module.End R M) - ∑ i ∈ Finset.range b, γ ^ i
      = (γ - 1) * -∑ i ∈ Finset.range b, ∑ j ∈ Finset.range i, γ ^ j := by
    rw [mul_neg, Finset.mul_sum]
    simp only [mul_geom_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    abel
  have hcomm : Commute (γ - 1) (-∑ i ∈ Finset.range b, ∑ j ∈ Finset.range i, γ ^ j) := by
    refine Commute.neg_right (Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => ?_)
    exact ((Commute.refl γ).sub_left (Commute.one_left γ)).pow_right j
  set Q := -∑ i ∈ Finset.range b, ∑ j ∈ Finset.range i, γ ^ j with hQ
  set e : Module.End R M := (b : Module.End R M) - ∑ i ∈ Finset.range b, γ ^ i with he
  set P : Submodule R M := LinearMap.range (γ - 1) with hP
  have hPI : P ≤ I • P := by
    rintro y ⟨z, rfl⟩
    have he1 : ∀ w ∈ P, e w = (b : R) • w := by
      rintro w ⟨v, rfl⟩
      rw [he, LinearMap.sub_apply, Module.End.natCast_apply, ← Module.End.mul_apply, hSN,
        LinearMap.zero_apply, sub_zero, Nat.cast_smul_eq_nsmul]
    have hek : ∀ k : ℕ, (e ^ k) ((γ - 1) z) = (b : R) ^ k • (γ - 1) z := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, Module.End.mul_apply, he1 _ ⟨z, rfl⟩, map_smul, ih, smul_smul, pow_succ,
          mul_comm]
    have hrange : LinearMap.range e ≤ P := by
      rw [hE, Module.End.mul_eq_comp]; exact LinearMap.range_comp_le_range _ _
    have hmap : ∀ w ∈ I • (⊤ : Submodule R M), e w ∈ I • P := by
      intro w hw
      have : (I • (⊤ : Submodule R M)).map e ≤ I • P := by
        rw [Submodule.map_smul'', Submodule.map_top]; exact Submodule.smul_mono le_rfl hrange
      exact this ⟨w, hw, rfl⟩
    have hr : (e ^ r) ((γ - 1) z) ∈ I • (⊤ : Submodule R M) := by
      rw [hE, hcomm.mul_pow, Module.End.mul_apply]; exact h _
    have hbig : (b : R) ^ (r + 1) • (γ - 1) z ∈ I • P := by
      rw [← hek, pow_succ', Module.End.mul_apply]; exact hmap _ hr
    have hsplit : (γ - 1) z = (1 - c * (b : R) ^ (r + 1)) • (γ - 1) z
        + c • ((b : R) ^ (r + 1) • (γ - 1) z) := by
      rw [smul_smul, ← add_smul, sub_add_cancel, one_smul]
    rw [hsplit]
    exact Submodule.add_mem _ (Submodule.smul_mem_smul hc ⟨z, rfl⟩) (Submodule.smul_mem _ c hbig)
  obtain ⟨t, ht1, ht0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I P
    (IsNoetherian.noetherian P) hPI
  have htne : t ≠ 0 := by
    rintro rfl
    apply hI
    rw [Ideal.eq_top_iff_one]
    simpa using I.neg_mem ht1
  ext x
  have hx := ht0 _ (LinearMap.mem_range_self (γ - 1) x)
  rw [smul_eq_zero_iff_right htne, LinearMap.sub_apply, sub_eq_zero] at hx
  simpa using hx

end GlobalTheory.Neat

theorem GlobalTheory.eq_one_of_finite_order_unipotent_mod_two_primes : ∀ (E : Type) [Field E] [NumberField E] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Finite (𝓞 E) Λ] [Module.IsTorsionFree (𝓞 E) Λ] (α : Λ →ₗ[𝓞 E] Λ) (m r g₁ g₂ : ℕ) (I₁ I₂ : Ideal (𝓞 E)), 0 < m → α ^ m = 1 → g₁.Prime → g₂.Prime → g₁ ≠ g₂ → I₁ ≠ ⊤ → I₂ ≠ ⊤ → (g₁ : 𝓞 E) ∈ I₁ → (g₂ : 𝓞 E) ∈ I₂ → (∀ x, ((α - 1) ^ r) x ∈ I₁ • (⊤ : Submodule (𝓞 E) Λ)) → (∀ x, ((α - 1) ^ r) x ∈ I₂ • (⊤ : Submodule (𝓞 E) Λ)) → α = 1 := by
  intro E _ _ Λ _ _ _ _ α m r g₁ g₂ I₁ I₂ hm hαm hg₁ hg₂ hne hI₁ hI₂ hg₁I hg₂I h₁ h₂
  have key : ∀ (p : ℕ) (I : Ideal (𝓞 E)), p.Prime → I ≠ ⊤ → (p : 𝓞 E) ∈ I →
      (∀ x, ((α - 1) ^ r) x ∈ I • (⊤ : Submodule (𝓞 E) Λ)) → ∃ a : ℕ, α ^ p ^ a = 1 := by
    intro p I hp hI hpI h
    obtain ⟨a, b, hpb, hmab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p hp.one_lt.ne'
    refine ⟨a, ?_⟩
    have hcop : Nat.Coprime p (b ^ (r + 1)) :=
      Nat.Coprime.pow_right _ ((hp.coprime_iff_not_dvd).2 hpb)
    obtain ⟨u, v, huv⟩ := Nat.Coprime.cast (R := 𝓞 E) hcop
    refine GlobalTheory.Neat.eq_one_of_unipotent_mod_of_unit I hI (α ^ p ^ a) b r ?_ v ?_
      (GlobalTheory.Neat.pow_prime_pow_unipotent I α hp hpI a r h)
    · rw [← pow_mul, ← hmab, hαm]
    · have : 1 - v * (b : 𝓞 E) ^ (r + 1) = u * p := by
        rw [← huv]; push_cast; ring
      rw [this]; exact I.mul_mem_left u hpI
  obtain ⟨a, ha⟩ := key g₁ I₁ hg₁ hI₁ hg₁I h₁
  obtain ⟨c, hc⟩ := key g₂ I₂ hg₂ hI₂ hg₂I h₂
  have hcop : Nat.Coprime (g₁ ^ a) (g₂ ^ c) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hg₁ hg₂).2 hne)
  have hd : orderOf α ∣ Nat.gcd (g₁ ^ a) (g₂ ^ c) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha) (orderOf_dvd_of_pow_eq_one hc)
  rw [hcop.gcd_eq_one] at hd
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_one hd)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqvCorMulCol
section
open Matrix Topology GlobalTheory.SmGL GlobalTheory.Whittaker

namespace GlobalTheory.JSW.Cut

open GlobalTheory.JSW.KirFin

theorem eqv_cor_mul_col {F : Type} [NormedField F] {ψ : AddChar F ℂ} {m : ℕ} {W : GL (Fin (m + 2)) F → ℂ}
    (hW : Eqv ψ W) (h : GL (Fin (m + 1)) F) (x : Fin (m + 1) → F) :
    W (cor h * mir 1 x) = ψ (lr h ⬝ᵥ x) * W (cor h) := by
  change W (mir h 0 * mir 1 x) = _
  rw [mir_mul, hW.apply_mir, mul_one, add_zero]
  rfl

theorem eqv_act {F : Type} [NormedField F] {ψ : AddChar F ℂ} {n : ℕ} {W : GL (Fin n) F → ℂ}
    (hW : Eqv ψ W) (T : GL (Fin n) F →₀ ℂ) : Eqv ψ (act T W) := fun u hu g => by
  unfold act
  rw [Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only
  rw [mul_assoc u, hW u hu]
  ring

theorem lr_ne_zero {F : Type} [NormedField F] {m : ℕ} (h : GL (Fin (m + 1)) F) : lr h ≠ 0 := fun h0 => by
  have h1 : lr (h * h⁻¹) = 0 := by rw [lr_mul, h0, zero_vecMul]
  rw [mul_inv_cancel] at h1
  have := congrFun h1 (Fin.last m)
  simp [lr] at this

end GlobalTheory.JSW.Cut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalAtMulTriangularIntVec
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section
namespace GlobalTheory.DefPt

theorem intVec_mem_nabla {n : ℕ} (la : Fin n → ℕ) (i : Idx la) : intVec la i ∈ nabla la ℤ := by
  have h := (Formalism.GradedWeylDivisibility.sSBasis ℤ n n la).choose_spec.1.2.1
  rw [nabla, ← h]
  exact Submodule.subset_span ⟨i, rfl⟩

def genUpperTri (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℤ) :=
  Matrix.of fun i j => if i ≤ j then X (i, j) else 0

theorem genUpperTri_blockTriangular (n : ℕ) : (genUpperTri n).BlockTriangular id := by
  intro i j hij
  simp only [genUpperTri, Matrix.of_apply]
  rw [if_neg (not_le.mpr (show j < i from hij))]

theorem colAct_intCast_of_mem {n : ℕ} {la : Fin n → ℕ} {f : Pol n ℤ} (hf : f ∈ nabla la ℤ)
    {S : Type} [CommRing S] (b : Matrix (Fin n) (Fin n) S) (hb : b.BlockTriangular id) :
    colAct b (map (Int.castRingHom S) f) = diagChar la b • map (Int.castRingHom S) f := by
  let ψ : MvPolynomial (Fin n × Fin n) ℤ →+* S := (aeval (R := ℤ) fun v : Fin n × Fin n => b v.1 v.2).toRingHom
  have hB : (genUpperTri n).map ψ = b := by
    ext i j
    simp only [Matrix.map_apply, genUpperTri, Matrix.of_apply]
    split_ifs with h
    · simp [ψ]
    · rw [map_zero, hb (show id j < id i from not_le.mp h)]
  have hgen := colAct_map_of_mem (Int.castRingHom (MvPolynomial (Fin n × Fin n) ℤ)) hf (genUpperTri n)
    (genUpperTri_blockTriangular n)
  have h2 := congrArg (map ψ) hgen
  rw [map_colAct, hB, map_map] at h2
  have hc : ψ.comp (Int.castRingHom (MvPolynomial (Fin n × Fin n) ℤ)) = Int.castRingHom S :=
    RingHom.ext_int _ _
  rw [hc] at h2
  rw [h2, smul_eq_C_mul, map_mul, map_C, map_map, hc, smul_eq_C_mul]
  congr 2
  simp only [diagChar, map_prod, map_pow, ← hB, Matrix.map_apply]

theorem evalAt_mul_triangular_intVec {n : ℕ} (la : Fin n → ℕ) (i : Idx la) {S : Type} [CommRing S]
    (y b : Matrix (Fin n) (Fin n) S) (hb : b.BlockTriangular id) :
    DualWeyl.evalAt (y * b) (map (Int.castRingHom S) (intVec la i)) =
      diagChar la b * DualWeyl.evalAt y (map (Int.castRingHom S) (intVec la i)) := by
  rw [← evalAt_colAct, colAct_intCast_of_mem (intVec_mem_nabla la i) b hb, smul_eq_C_mul, map_mul]
  simp [DualWeyl.evalAt]

theorem tval_mul_triangular : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ) (S : Type) [CommRing S] (x : TIdx la → S) (y b : ∀ t, Matrix (Fin (N t)) (Fin (N t)) S), (∀ t, (b t).BlockTriangular id) → tval la x (fun t => y t * b t) = (∏ t, diagChar (la t) (b t)) * tval la x y := by
  intro T _ _ N la S _ x y b hb
  unfold tval
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  simp only [evalAt_mul_triangular_intVec _ _ _ _ (hb _), Finset.prod_mul_distrib]
  ring

end GlobalTheory.DefPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeQuotientByFiniteTranslations
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.TranslQuotient

theorem finiteSubsets_preimage {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (hL : L.IsLB)
    (hamp : Out.RelAmple A L) (U : S.Opens) (hU : IsAffineOpen U) :
    FiniteSubsetsInAffineOpens (A.hom ⁻¹ᵁ U) := by
  have h := GlobalTheory.isAmpleLB_of_relAmple A hL hamp U hU
  exact ⟨fun s hs => by
    obtain ⟨n, -, t, h1, -, h2⟩ := h.exists_affine_finite_subset hs (U := ⊤) (Set.subset_univ _)
    exact ⟨_, h2, h1⟩⟩

theorem transl_mul {S : Scheme.{0}} {A : Over S} [GrpObj A] (a c : 𝟙_ (Over S) ⟶ A) :
    Hecke.transl (a * c) = Hecke.transl a ≫ Hecke.transl c := by
  simp only [Hecke.transl, comp_mul, Category.id_comp, Category.comp_id]
  rw [← Category.assoc, toUnit_unique (_ ≫ toUnit A) (toUnit A)]
  exact (mul_assoc _ _ _).symm

theorem transl_one {S : Scheme.{0}} {A : Over S} [GrpObj A] :
    Hecke.transl (1 : 𝟙_ (Over S) ⟶ A) = 𝟙 A := by
  simp [Hecke.transl]

theorem isAbelianScheme_of_finite_etale {S : Scheme.{0}} (A Q : Over S) [GrpObj A] [GrpObj Q]
    (q : A ⟶ Q) (hA : IsAbelianScheme A) (hQ : IsCommMonObj Q) (hfin : IsFinite q.left)
    (het : Etale q.left) (hsurj : Surjective q.left) : IsAbelianScheme Q := by
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hw : q.left ≫ Q.hom = A.hom := Over.w q
  have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom
    hA.smooth hA.geomConnected
  have : Flat (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : UniversallyClosed (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : IsSeparated (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyReduced (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyConnected (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : LocallyOfFinitePresentation (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have := GlobalTheory.flat_of_comp_of_flat_of_surjective q.left Q.hom
  have := UniversallyClosed.of_comp_surjective q.left Q.hom
  have := GlobalTheory.NilProper.isSeparated_of_comp_surjective q.left Q.hom
  have := GlobalTheory.AbelianQuotient.geometricallyReduced_of_comp q.left Q.hom
  have : LocallyOfFinitePresentation Q.hom :=
    _root_.GlobalTheory.CompanionTheory.LfpDescent.descends q.left Q.hom hfin inferInstance inferInstance hsurj inferInstance
  exact ⟨hQ, GlobalTheory.AbelianQuotient.smooth_of_grpObj_of_flat Q, ⟨⟩,
    GlobalTheory.AbelianQuotient.geometricallyConnected_of_comp q.left Q.hom⟩


open GlobalTheory.AbelianQuotient in
theorem grp_descent : ∀ (S : Scheme.{0}) (A Q : Over S) [GrpObj A] [IsCommMonObj A] (q : A ⟶ Q),
    Flat q.left → Surjective q.left → QuasiCompact q.left →
    (∀ (W : Over S) (a b c d : W ⟶ A), a ≫ q = b ≫ q → c ≫ q = d ≫ q → (a * c) ≫ q = (b * d) ≫ q) →
    ∃ _ : GrpObj Q, IsCommMonObj Q ∧ IsMonHom q := by
  intro S A Q _ _ q _ _ _ hq
  have hinv : ∀ {W : Over S} (a b : W ⟶ A), a ≫ q = b ≫ q → a⁻¹ ≫ q = b⁻¹ ≫ q := by
    intro W a b h
    have h1 : (a⁻¹ * a) ≫ q = (a⁻¹ * b) ≫ q := hq W _ _ _ _ rfl h
    have h2 := hq W b⁻¹ b⁻¹ (a⁻¹ * b) (a⁻¹ * a) rfl h1.symm
    have e1 : b⁻¹ * (a⁻¹ * b) = a⁻¹ := by rw [mul_left_comm, inv_mul_cancel, _root_.mul_one]
    have e2 : b⁻¹ * (a⁻¹ * a) = b⁻¹ := by rw [inv_mul_cancel, _root_.mul_one]
    rwa [e1, e2] at h2
  have hμ : ∀ {W : Over S} (x : W ⟶ A ⊗ A), x ≫ μ[A] = (x ≫ fst A A) * (x ≫ snd A A) := by
    intro W x
    rw [Hom.mul_def, ← comp_lift, lift_fst_snd, Category.comp_id]
  have := flat_tensorHom q q
  have := surjective_tensorHom q q
  have := quasiCompact_tensorHom q q
  have := FlatQuotient.epi_of_flat_surjective q
  have := FlatQuotient.epi_tensorHom q q
  have := FlatQuotient.epi_tensorHom (q ⊗ₘ q) q
  obtain ⟨m, hm⟩ := exists_desc (q ⊗ₘ q) (μ[A] ≫ q) (by
    intro W a b h
    have h1 : (a ≫ fst A A) ≫ q = (b ≫ fst A A) ≫ q := by simpa using h =≫ fst Q Q
    have h2 : (a ≫ snd A A) ≫ q = (b ≫ snd A A) ≫ q := by simpa using h =≫ snd Q Q
    rw [← Category.assoc, ← Category.assoc, hμ a, hμ b]
    exact hq W _ _ _ _ h1 h2)
  obtain ⟨n, hn⟩ := exists_desc q (GrpObj.inv ≫ q) (by
    intro W a b h
    rw [← Category.assoc, ← Category.assoc, ← Hom.inv_def, ← Hom.inv_def]
    exact hinv a b h)
  have key : ∀ {W : Over S} (a b : W ⟶ A), lift (a ≫ q) (b ≫ q) ≫ m = (a * b) ≫ q := by
    intro W a b
    rw [← lift_map, Category.assoc, hm, Hom.mul_def, Category.assoc]
  letI : MonObj Q :=
    { one := η[A] ≫ q
      mul := m
      one_mul := by
        rw [← cancel_epi (λ_ Q).inv, ← cancel_epi q]
        have := key (1 : A ⟶ A) (𝟙 A)
        rw [_root_.one_mul] at this
        rw [Iso.inv_hom_id, Category.comp_id]
        refine Eq.trans ?_ (this.trans (Category.id_comp _))
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        ext <;> simp [Hom.one_def]
      mul_one := by
        rw [← cancel_epi (ρ_ Q).inv, ← cancel_epi q]
        have := key (𝟙 A) (1 : A ⟶ A)
        rw [_root_.mul_one] at this
        rw [Iso.inv_hom_id, Category.comp_id]
        refine Eq.trans ?_ (this.trans (Category.id_comp _))
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        ext <;> simp [Hom.one_def]
      mul_assoc := by
        rw [← cancel_epi ((q ⊗ₘ q) ⊗ₘ q)]
        have h1 : ((q ⊗ₘ q) ⊗ₘ q) ≫ m ▷ Q = (μ[A] ▷ A) ≫ (q ⊗ₘ q) := by
          rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
            hm, Category.comp_id, Category.id_comp]
        have h2 : ((q ⊗ₘ q) ⊗ₘ q) ≫ (α_ Q Q Q).hom ≫ Q ◁ m =
            (α_ A A A).hom ≫ (A ◁ μ[A]) ≫ (q ⊗ₘ q) := by
          rw [associator_naturality_assoc]
          congr 1
          ext <;> simp [hm]
        rw [reassoc_of% h1, reassoc_of% h2, hm, MonObj.mul_assoc_assoc] }
  have hhom : IsMonHom q := ⟨rfl, hm.symm⟩
  letI : GrpObj Q :=
    { inv := n
      left_inv := by
        rw [← cancel_epi q, comp_lift_assoc, hn, Category.comp_id]
        have := key GrpObj.inv (𝟙 A)
        rw [Category.id_comp] at this
        refine this.trans ?_
        rw [Hom.mul_def, GrpObj.left_inv, comp_toUnit_assoc, Category.assoc]
        rfl
      right_inv := by
        rw [← cancel_epi q, comp_lift_assoc, hn, Category.comp_id]
        have := key (𝟙 A) GrpObj.inv
        rw [Category.id_comp] at this
        refine this.trans ?_
        rw [Hom.mul_def, GrpObj.right_inv, comp_toUnit_assoc, Category.assoc]
        rfl }
  refine ⟨inferInstance, ⟨?_⟩, hhom⟩
  rw [← cancel_epi (q ⊗ₘ q), BraidedCategory.braiding_naturality_assoc, ← IsMonHom.mul_hom,
    IsCommMonObj.mul_comm_assoc]

theorem comp_transl {S : Scheme.{0}} {A W : Over S} [GrpObj A] (x : W ⟶ A) (h : 𝟙_ (Over S) ⟶ A) :
    x ≫ Hecke.transl h = x * (toUnit _ ≫ h) := by
  rw [Hecke.transl, comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit A) (toUnit _)]

theorem transl_compat : ∀ (S : Scheme.{0}) (A Q : Over S) [GrpObj A] [IsCommMonObj A]
    (H : Subgroup (𝟙_ (Over S) ⟶ A)) (q : A ⟶ Q),
    GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) q.left →
    ∀ (W : Over S) (a b c d : W ⟶ A), a ≫ q = b ≫ q → c ≫ q = d ≫ q → (a * c) ≫ q = (b * d) ≫ q := by
  intro S A Q _ _ H q hc W a b c d hab hcd
  have loc := (GlobalTheory.ZM.galoisCover_descent _ _ _ _ _ hc).2.1
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ fun p ↦ ?_
  obtain ⟨V₁, h, hp₁, e₁⟩ := loc W.left a.left b.left (congrArg CommaMorphism.left hab) p
  obtain ⟨V₂, k, hp₂, e₂⟩ := loc W.left c.left d.left (congrArg CommaMorphism.left hcd) p
  refine ⟨V₁ ⊓ V₂, ⟨hp₁, hp₂⟩, ?_⟩
  let jV : Over.mk ((V₁ ⊓ V₂).ι ≫ W.hom) ⟶ W := Over.homMk (V₁ ⊓ V₂).ι rfl
  have f₁ : jV ≫ b = (jV ≫ a) * (toUnit _ ≫ h.1) := by
    rw [← comp_transl, Category.assoc]
    ext
    simp only [Over.comp_left, Over.homMk_left, jV]
    rw [← W.left.homOfLE_ι (inf_le_left : V₁ ⊓ V₂ ≤ V₁), ]
    simp only [Category.assoc, e₁]
  have f₂ : jV ≫ d = (jV ≫ c) * (toUnit _ ≫ k.1) := by
    rw [← comp_transl, Category.assoc]
    ext
    simp only [Over.comp_left, Over.homMk_left, jV]
    rw [← W.left.homOfLE_ι (inf_le_right : V₁ ⊓ V₂ ≤ V₂), ]
    simp only [Category.assoc, e₂]
  have hinv : Hecke.transl (h * k).1 ≫ q = q := Over.OverMorphism.ext (hc.inv (h * k))
  have key : jV ≫ (b * d) = jV ≫ (a * c) ≫ Hecke.transl (h * k).1 := by
    rw [comp_mul, f₁, f₂, ← Category.assoc, comp_transl, comp_mul, Subgroup.coe_mul, comp_mul,
      _root_.mul_mul_mul_comm]
  have key' : jV ≫ (a * c) ≫ q = jV ≫ (b * d) ≫ q := by
    rw [← Category.assoc jV (b * d), key, Category.assoc, Category.assoc, hinv]
  simpa [jV] using congrArg CommaMorphism.left key'

theorem exists_quotient : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (H : Subgroup (𝟙_ (Over S) ⟶ A)), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Finite H → (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (h : 𝟙_ (Over S) ⟶ A), h ∈ H → toUnit (Over.mk x) ≫ h = 1 → h = 1) → ∃ (A' : Over S) (_ : GrpObj A') (_ : IsCommMonObj A') (ψ : A ⟶ A'), IsAbelianScheme A' ∧ IsMonHom ψ ∧ GlobalTheory.ZM.IsGaloisCover H (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left := by
  intro S A _ _ L H hA hL hamp hH hfree
  let ρ : H → (A.left ⟶ A.left) := fun h => (Hecke.transl h.1).left
  have h1 : ρ 1 = 𝟙 _ := by
    show (Hecke.transl (1 : 𝟙_ (Over S) ⟶ A)).left = _
    rw [transl_one]; rfl
  have hm : ∀ a c, ρ (a * c) = ρ a ≫ ρ c := fun a c => by
    show (Hecke.transl (a.1 * c.1)).left = _
    rw [transl_mul]; rfl
  have hS : ∀ a, ρ a ≫ A.hom = A.hom := fun a => Over.w _
  let τ := GlobalTheory.ZM.autOfRightAction ρ h1 hm
  have hτ : ∀ a, (τ a).asIso.hom ≫ A.hom = A.hom := fun a => hS a⁻¹
  have : OrbitsInAffineOpens τ := OrbitsInAffineOpens.of_locally_on_base τ A.hom hτ fun s => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hsU, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
    exact ⟨U, hsU, finiteSubsets_preimage A L hL hamp U hU⟩
  have hfreeρ : ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Spec (.of k) ⟶ A.left) (a : H),
      y ≫ ρ a = y → a = 1 := by
    intro k _ _ y a hy
    let y' : Over.mk (y ≫ A.hom) ⟶ A := Over.homMk y rfl
    have e : y' ≫ Hecke.transl a.1 = y' := Over.OverMorphism.ext hy
    have e' : y' ≫ Hecke.transl a.1 = y' * (toUnit _ ≫ a.1) := by
      rw [Hecke.transl, comp_mul, Category.comp_id, ← Category.assoc,
        toUnit_unique (y' ≫ toUnit A) (toUnit _)]
    rw [e'] at e
    have h2 : toUnit (Over.mk (y ≫ A.hom)) ≫ a.1 = 1 := mul_eq_left.mp e
    exact Subtype.ext (hfree k (y ≫ A.hom) a.1 a.2 h2)
  have hf : IsFreeAction τ := .of_isAlgClosed fun k _ _ y a h ↦ inv_eq_one.mp (hfreeρ k y a⁻¹ h)
  obtain ⟨Y, π, hQ⟩ := (GlobalTheory.exists_isAffineQuotient_iff τ).mpr ‹OrbitsInAffineOpens τ›
  let ψ : A ⟶ Over.mk (hQ.desc A.hom hτ) :=
    Over.homMk π (hQ.comp_desc A.hom hτ)
  have hc : GlobalTheory.ZM.IsGaloisCover H ρ ψ.left := by
    refine ⟨hH, h1, hm, fun a ↦ ?_, hQ.isFinite_of_isFreeAction hf,
      hQ.etale_of_isFreeAction hf, hQ.surjective, fun k _ _ y y' e ↦ ?_⟩
    · have := hQ.comp_eq a⁻¹
      rwa [GlobalTheory.ZM.autOfRightAction_hom, inv_inv] at this
    · obtain ⟨a, ha⟩ := (hQ.comp_eq_comp_iff y y').mp e
      have ha : y ≫ ρ a⁻¹ = y' := ha
      refine ⟨a⁻¹, ha, fun c hc ↦ ?_⟩
      have hc : y ≫ ρ c = y' := hc
      have : y ≫ ρ (c * a) = y := by
        rw [hm, reassoc_of% hc, ← ha, Category.assoc, ← hm, inv_mul_cancel, h1, Category.comp_id]
      exact eq_inv_of_mul_eq_one_left (hfreeρ k y _ this)
  have := hc.fin
  have := hc.etale
  have := hc.onto
  obtain ⟨inst, hcomm, hhom⟩ := grp_descent S A _ ψ inferInstance hc.onto inferInstance
    (transl_compat S A _ H ψ hc)
  exact ⟨_, inst, hcomm, ψ, isAbelianScheme_of_finite_etale A _ ψ hA hcomm hc.fin hc.etale hc.onto,
    hhom, hc⟩

end GlobalTheory.TranslQuotient

end
end

