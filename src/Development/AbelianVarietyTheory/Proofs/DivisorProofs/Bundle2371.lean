module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1190
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0294
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefLineBundleNumericalTheoremsProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1325
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Interchange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section

namespace GlobalTheory.PolTensBimult

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TensCub

theorem interchange {U X : Type} [CommGroup U] [AddCommGroup X] (t : X → X → U) (hs : ∀ u v, t u v = t v u)
    (hc : ∀ u u' v, t u' v * (t (u + u') v)⁻¹ * t u v = t v u' * (t (u + v) u')⁻¹ * t u u') (x x' y y' : X) :
    t (x + x') (y + y') * (t x y)⁻¹ * (t x' y')⁻¹ = t (x + y) (x' + y') * (t x x')⁻¹ * (t y y')⁻¹ := by
  have h₁ := hc y y' (x + x')
  have h₂ := hc x' y' (x + y)
  have h₃ := hc x x' y
  rw [hs (y + y'), hs y' (x + x'), hs y (x + x')] at h₁
  rw [hs (x' + y'), hs y' (x + y), hs x' (x + y), show x' + (x + y) = y + (x + x') by abel] at h₂
  rw [hs y x'] at h₃
  have k₁ := congrArg Additive.ofMul h₁
  have k₂ := congrArg Additive.ofMul h₂
  have k₃ := congrArg Additive.ofMul h₃
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at k₁ k₂ k₃ ⊢
  rw [← sub_eq_zero] at k₁ k₂ k₃ ⊢
  have k := congrArg₂ (· - ·) (congrArg₂ (· - ·) k₂ k₁) k₃
  simp only [sub_zero] at k
  rw [← k]
  abel

theorem alg {U X X' : Type} [CommGroup U] [AddCommGroup X] [AddCommGroup X'] {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (e : X' ≃+ (Fin r → X)) (O ψ' : X' → U) (τ' : X' → X' → U) (t : X → X → U) (c' rig' : U)
    (a a' b : X') (h0 : t 0 0 = 1)
    (ht : ∀ x x' y y', t (x + x') (y + y') * (t x y)⁻¹ * (t x' y')⁻¹ = t (x + y) (x' + y') * (t x x')⁻¹ * (t y y')⁻¹)
    (hψ : ∀ u, ψ' u = O u * ∏ i, ∏ j, t (e u i) (e u j) ^ W i j)
    (hτ : ∀ u v, τ' u v = ψ' (u + v) * (ψ' u)⁻¹ * (ψ' v)⁻¹ * rig'⁻¹) (hr : ψ' 0 * rig' = 1)
    (hc : c' * (O (a + a' + b) * (O (a + a'))⁻¹ * (O (a + b))⁻¹ * (O (a' + b))⁻¹ * O a * O a' * O b * (O 0)⁻¹) =
      ∏ k : (Fin r × Fin r) × Fin 4,
        (t (![e a k.1.1 + e a k.1.2, e a k.1.1, e a k.1.2, 0] k.2) (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2) *
          t (![e a' k.1.1 + e a' k.1.2, e a' k.1.1, e a' k.1.2, 0] k.2) (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2) *
          (t (![e a k.1.1 + e a k.1.2, e a k.1.1, e a k.1.2, 0] k.2 + ![e a' k.1.1 + e a' k.1.2, e a' k.1.1, e a' k.1.2, 0] k.2)
            (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2))⁻¹) ^ tensε W k) :
    τ' (a + a') b * c' = τ' a b * τ' a' b := by
  have hr' : rig'⁻¹ = ψ' 0 := (eq_inv_of_mul_eq_one_right hr).symm ▸ inv_inv _
  have hτ' : ∀ u v, τ' u v = O (u + v) * (O u)⁻¹ * (O v)⁻¹ * O 0 *
      ∏ i, ∏ j, (t (e u i + e u j) (e v i + e v j) * (t (e u i) (e v i))⁻¹ * (t (e u j) (e v j))⁻¹) ^ W i j := by
    intro u v
    rw [hτ, hr']
    simp only [hψ, map_add (f := _), Pi.add_apply, map_zero, Pi.zero_apply, h0, one_zpow, Finset.prod_const_one, ← ht (e u _) (e v _)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_prod, ofMul_zpow, smul_add, smul_neg, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, ofMul_one]
    abel
  rw [eq_mul_inv_of_mul_eq hc, hτ', hτ', hτ']
  simp only [Fintype.prod_prod_type, Fin.prod_univ_four, tensε, Oε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_add, Pi.add_apply,
    add_zero, h0]
  have e1 : ∀ i j, e a i + e a j + (e a' i + e a' j) = e a i + e a' i + (e a j + e a' j) := fun i j => by abel
  simp only [e1]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_prod, ofMul_zpow, smul_add, smul_neg, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, _root_.mul_one, mul_neg, neg_smul, ofMul_one, smul_zero, Finset.sum_const_zero]
  abel

theorem cubV_prod (hG : GlobalFnsSt) {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (hA : IsAbelianScheme A) {M' : RigLB A} {M : RigLB B} (c' : CubicalStr A M') (c : CubicalStr B M) {N : Type} [Fintype N]
    (P : N → (A ⟶ B)) (hP : ∀ k, IsMonHom (P k)) (φ : N → (A.left ⟶ B.left)) (hφ : ∀ k, (P k).left = φ k) (n : N → ℤ)
    (w : LB.Iso M'.L (LB.LinComb M.L φ n)) (hw : w.IsGen) {T : Over S} (z : T.left) (J J') (hJ : Good M.L z J)
    (hJ' : Good M'.L z J') (x x' y : T ⟶ A) (om : (T ⟶ A) → (T.left.presheaf.stalk z)ˣ)
    (hom : om = fun p => bwg w p.left z (fun k => J (p.left ≫ φ k)) (J' p.left)) :
    cubV c' z J' x x' y * (om (x * x' * y) * (om (x * x'))⁻¹ * (om (x * y))⁻¹ * (om (x' * y))⁻¹ * om x * om x' * om y *
      (om 1)⁻¹) = ∏ k, cubV c z J (x ≫ P k) (x' ≫ P k) (y ≫ P k) ^ n k := by
  subst hom
  let ρ : N → ((G3 A).left ⟶ (G3 B).left) := fun k => (P k ⊗ₘ P k ⊗ₘ P k).left
  have hψ : ∀ k a, thφ A (x3 A) a ≫ φ k = ρ k ≫ thφ B (x3 B) a := fun k a => by
    rw [← hφ k]
    letI := hP k
    exact (CubeMap.ofHom (P k)).psum_comm a.down
  have hρ : ∀ {T : Over S} (a b c : T ⟶ A) k, (lift a (lift b c)).left ≫ ρ k =
      (lift (a ≫ P k) (lift (b ≫ P k) (c ≫ P k))).left := fun a b c k => by
    show (lift a (lift b c) ≫ (P k ⊗ₘ P k ⊗ₘ P k)).left = _
    rw [lift_map, lift_map]
  let e : 𝟙_ (Over S) ⟶ G3 A := lift 1 (lift 1 1)
  have sj : Function.Surjective ((snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom).appTop.hom :=
    surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2)
  have he : e.left ≫ (snd A (A ⊗ A)).left ≫ (snd A A).left ≫ A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := box_unique (pr := φ) (εp := n) M.isLB M'.isLB w hw (ε := thε) hψ
    c'.isGen c.isGen _ e.left he sj (fun s I I' hI hI' => by
      have C' : IsCub (cubV c' (T := 𝟙_ (Over S)) s I') := isCub_cubV c' hI'
      have C : IsCub (cubV c (T := 𝟙_ (Over S)) s I) := isCub_cubV c hI
      have p := prod_cub (1 : 𝟙_ (Over S) ⟶ A) 1 1
        (fun q => bwg w q s (fun i => I (q ≫ φ i)) (I' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine (congrArg₂ (· * ·) p (C'.face 1 1)).trans (Eq.trans (by simp) (Finset.prod_eq_one fun k _ => ?_).symm)
      have := hP k
      have o : (1 : 𝟙_ (Over S) ⟶ A) ≫ P k = 1 := by simp [Hom.one_def]
      rw [show e.left ≫ ρ k = _ from hρ 1 1 1 k, o]
      exact (congrArg (· ^ n k) (C.face 1 1)).trans (one_zpow _)) _ (lift x (lift x' y)).left z J J' hJ hJ'
  have p := prod_cub x x' y (fun q => bwg w q z (fun i => J (q ≫ φ i)) (J' q))
  refine (mul_comm _ _).trans ((congrArg₂ (· * ·) p rfl).symm.trans (key.trans (Finset.prod_congr rfl fun k _ => ?_)))
  rw [hρ]; rfl

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)), IsTens Q D' W pr xe → (∀ (z : (TK R).left) (J : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (D'.psi 0) (𝟙 _) z J * val D'.rigK (𝟙 _) z J = 1) → D'.TauBimult := by
  intro R _ _ _ _ Q D' r W pr xe T hn a a' b
  obtain ⟨hpr, -, hcp, w, hw, hpsi⟩ := T
  have hG : GlobalFnsSt := GlobalTheory.lawsAndExpansions.1.1.globalFns
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ : ∃ J, Good Q.M.L y J :=
    ⟨fun ψ => (exists_chart Q.M.isLB (ψ y)).choose, fun ψ => (exists_chart Q.M.isLB (ψ y)).choose_spec⟩
  let P : (Fin r × Fin r) × Fin 4 → (D'.P.A ⟶ Q.B) := fun k => ![pr k.1.1 * pr k.1.2, pr k.1.1, pr k.1.2, 1] k.2
  have hPh : ∀ k, IsMonHom (P k) := by
    rintro ⟨⟨i, j⟩, m⟩
    have := hpr i
    have := hpr j
    fin_cases m
    · exact GlobalTheory.Serre.isMonHom_mul _ _
    · exact hpr i
    · exact hpr j
    · exact GlobalTheory.Serre.isMonHom_one
  have hPl : ∀ k, (P k).left = tensφ pr k := by
    rintro ⟨⟨i, j⟩, m⟩
    fin_cases m <;> rfl
  have key := cubV_prod hG D'.P.isAb D'.cub Q.cub P hPh (tensφ pr) hPl (tensε W) w hw (T := TK R) y J J' hJ hJ'
    (cP D' _ a) (cP D' _ a') (cP D' _ b) _ rfl
  have hψ : ∀ u, val (D'.psi u) (𝟙 _) y J' = bwg w (cP D' (TK R) u).left y (fun k => J ((cP D' (TK R) u).left ≫ tensφ pr k)) (J' (cP D' (TK R) u).left) * ∏ i, ∏ j, val (Q.tau (xe u i) (xe u j)) (𝟙 _) y J ^ W i j :=
    fun u => hpsi u y J J' hJ hJ'
  have vt : ∀ u v, val (D'.tau u v) (𝟙 _) y J' = val (D'.psi (u + v)) (𝟙 _) y J' * (val (D'.psi u) (𝟙 _) y J')⁻¹ * (val (D'.psi v) (𝟙 _) y J')⁻¹ * (val D'.rigK (𝟙 _) y J')⁻¹ := by
    intro u v; simp only [DegPre.tau, val_mul hJ', val_inv]
  have c0 : cP D' (TK R) 0 = 1 := by
    have := cPoint_add D' (TK R) 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have q0 : Q.c 0 = 1 := mul_eq_left.1 ((Q.c_add 0 0).symm.trans (by rw [add_zero]))
  have hP : ∀ u k, cP D' (TK R) u ≫ P k = toUnit (TK R) ≫ Q.c (![xe u k.1.1 + xe u k.1.2, xe u k.1.1, xe u k.1.2, 0] k.2) := by
    intro u k
    have e : ∀ i, cP D' (TK R) u ≫ pr i = toUnit (TK R) ≫ Q.c (xe u i) := fun i => by
      rw [cP, Category.assoc, hcp]
    obtain ⟨⟨i, j⟩, m⟩ := k
    fin_cases m
    · show cP D' (TK R) u ≫ (pr i * pr j) = toUnit (TK R) ≫ Q.c (xe u i + xe u j)
      rw [MonObj.comp_mul, e, e, Q.c_add, MonObj.comp_mul]
    · exact e i
    · exact e j
    · show cP D' (TK R) u ≫ 1 = toUnit (TK R) ≫ Q.c 0
      rw [q0, MonObj.comp_one, MonObj.comp_one]
  rw [GlobalTheory.TauBimultBox.val_lhs D' hJ' a a' b, val_mul hJ']
  have hC : ∀ u u' v, cubV Q.cub y J (toUnit (TK R) ≫ Q.c u) (toUnit (TK R) ≫ Q.c u') (toUnit (TK R) ≫ Q.c v) = val (Q.tau u v) (𝟙 _) y J * val (Q.tau u' v) (𝟙 _) y J * (val (Q.tau (u + u') v) (𝟙 _) y J)⁻¹ := fun u u' v => by
    rw [← Q.tau_add u u' v y J hJ, mul_comm, inv_mul_cancel_left]
  have hI := interchange (fun u v => val (Q.tau u v) (𝟙 _) y J) (fun u v => Q.tau_symm u v y J hJ) (fun u u' v => by
    have := (isCub_cubV Q.cub hJ).s12 (toUnit (TK R) ≫ Q.c u) (toUnit (TK R) ≫ Q.c u') (toUnit (TK R) ≫ Q.c v)
    rw [hC, hC, _root_.mul_assoc, _root_.mul_assoc, mul_comm, mul_comm (val (Q.tau u _) (𝟙 _) y J)] at this
    first | exact this | exact this.symm)
  simp only [hP, hC] at key
  have h1 : cP D' (TK R) a * cP D' (TK R) a' * cP D' (TK R) b = cP D' (TK R) (a + a' + b) := by rw [cPoint_add, cPoint_add]
  have h2 : cP D' (TK R) a * cP D' (TK R) a' = cP D' (TK R) (a + a') := (cPoint_add _ _ _ _).symm
  have h3 : cP D' (TK R) a * cP D' (TK R) b = cP D' (TK R) (a + b) := (cPoint_add _ _ _ _).symm
  have h4 : cP D' (TK R) a' * cP D' (TK R) b = cP D' (TK R) (a' + b) := (cPoint_add _ _ _ _).symm
  rw [h1, h2, h3, h4, ← c0] at key
  refine alg W xe
    (fun u => bwg w (cP D' (TK R) u).left y (fun k => J ((cP D' (TK R) u).left ≫ tensφ pr k)) (J' (cP D' (TK R) u).left))
    (fun u => val (D'.psi u) (𝟙 _) y J') (fun u v => val (D'.tau u v) (𝟙 _) y J') (fun u v => val (Q.tau u v) (𝟙 _) y J)
    (cubV D'.cub y J' (cP D' (TK R) a) (cP D' (TK R) a') (cP D' (TK R) b)) (val D'.rigK (𝟙 _) y J') a a' b
    (Q.val_tau_zero 0 y J hJ) hI hψ vt (hn y J' hJ') ?_
  beta_reduce
  exact key

end GlobalTheory.PolTensBimult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleOfOrdOne
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.AdjCodimTwo

theorem irreducible_of_ord_one {k K : Type} [Field k] [Field K] {c : k →+* K} (P : Place c)
    (x : P.ring) (hx : P.ord (x : K) = 1) : Irreducible x := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [Place.ord] at hx
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible P.ring
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
  have hπ0 : (π : K) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hv0 : ((v : P.ring) : K) ≠ 0 := fun h => v.ne_zero (Subtype.ext h)
  have e : P.ord (((v : P.ring) * π ^ n : P.ring) : K) = n := by
    push_cast
    rw [P.ord_mul hv0 (pow_ne_zero _ hπ0), P.ord_eq_zero v.isUnit, P.ord_pow, P.ord_irreducible hπ]
    simp
  rw [e] at hx
  obtain rfl : n = 1 := by exact_mod_cast hx
  rw [pow_one]
  exact (irreducible_isUnit_mul v.isUnit).2 hπ

theorem disc_residue_eq : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q)
  (S E : Place cL) (ψ : S.ring →+* K) (f : S.ring) (w : Fin n → S.ring) (θ : S.ring →₀ ℚ),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) →
  ringKrullDim Q = 2 → S.IsPrimeOf Q → E.IsPrimeOf Q → S.ord (t : L) = 1 → E.ord (u : L) = 1 →
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → Irreducible f → TrBasis cK (fun i => ψ (w i)) →
  (∀ g ∈ θ.support, ψ g ≠ 0) →
  (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring →
    P.disc (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
      (Finsupp.mapDomain (fun g : S.ring => (g : L)) θ + Finsupp.single (f : L) 1) = 0) →
  ∃ F : Place cK, (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) ∧
    F.disc (dForm cK (fun i => ψ (w i))) (Finsupp.mapDomain ψ θ) =
      E.disc (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L))
        (Finsupp.mapDomain (fun g : S.ring => (g : L)) θ + Finsupp.single (f : L) 1) := by
  intro L K _ _ cL cK n Q hQ t u S E ψ f w θ hm hd hS hE hSt hEu hψ hc hf hw hθ hP
  classical
  obtain ⟨hA1, hA2⟩ := GlobalTheory.T.twoDimLocalModel_primePlaces_along_parameters cL Q hQ t u hm hd
  obtain ⟨m, z, hzU, hzG⟩ := GlobalTheory.T.isFreeModuleGenerator_kaehlerWedge_regularPair_cons cL Q hQ t u hm hd
  have hxe : (fun i => ((Fin.cons t (Fin.cons u z : Fin (m + 1) → Q) : Fin (m + 2) → Q) i : L)) =
      (Fin.cons (t : L) (Fin.cons (u : L) (fun i => (z i : L)) : Fin (m + 1) → L) : Fin (m + 2) → L) := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => rfl) j
  have hzT := _root_.GlobalTheory.FieldPair.trBasis_of_isFreeGen_dForm cL Q hQ _ _ (by omega) hzG
  have hzO := _root_.GlobalTheory.formOrd_dForm_of_isPrimeOf cL Q hQ _ _ hzG
  rw [hxe] at hzT hzO
  obtain ⟨F, hFr, hFu⟩ := GlobalTheory.T.exists_residuePlace_of_twoDimLocalModel cL cK Q hQ t u hm hd S ψ hS hSt hψ hc
  have hQS : ∀ q : Q, (q : L) ∈ S.ring := fun q => hS.1 q q.2
  let us : S.ring := ⟨u, hQS u⟩
  let ts : S.ring := ⟨t, hQS t⟩
  let zs : Fin m → S.ring := fun i => ⟨z i, hQS (z i)⟩
  have hF1 : F.ord (ψ us) = 1 := hFu us rfl
  have hB4 := _root_.GlobalTheory.FieldPair.eval₂_residue_ne_zero_and_inv_mem_of_isUnit cL cK Q hQ S ψ F hS.1 hc hFr m z zs (fun _ => rfl) hzU
  have hzF : ∀ i, ψ (zs i) ∈ F.ring := fun i => (hFr _).2 ⟨zs i, (z i).2, rfl⟩
  have hTK := _root_.GlobalTheory.FieldPair.ResidueTrBasis.trBasis_cons cL cK S ψ hψ hc F m (ψ us) (fun i => ψ (zs i)) ⟨_, hzT⟩ hF1 hzF hB4
  have hFO := _root_.GlobalTheory.formOrd_dForm_cons_of_ord_eq_one cK F m (ψ us) (fun i => ψ (zs i)) hF1 hzF hB4 hTK
  obtain rfl : n = m + 1 := by
    letI := cK.toAlgebra
    have h1 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hw
    have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hTK
    rw [Cardinal.mk_fin] at h1 h2
    exact_mod_cast h1.trans h2.symm
  let v : Fin (m + 1) → S.ring := Fin.cons us zs
  have hv : (fun i => ψ (v i)) = (Fin.cons (ψ us) (fun i => ψ (zs i)) : Fin (m + 1) → K) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have htv : (Fin.cons (ts : L) (fun i => (v i : L)) : Fin (m + 2) → L) =
      (Fin.cons (t : L) (Fin.cons (u : L) (fun i => (z i : L)) : Fin (m + 1) → L) : Fin (m + 2) → L) := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun _ => rfl) j
  set Ω0 := (dForm cL (Fin.cons (t : L) (Fin.cons (u : L) (fun i => (z i : L)) : Fin (m + 1) → L) : Fin (m + 2) → L)) with hΩ0
  set η := dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (m + 1 + 1) → L) with hη
  have hfreeL := (_root_.GlobalTheory.FieldPair.formOrd_api cL (m + 2) _ hzT).1
  obtain ⟨H, hH⟩ := hfreeL.2 η
  have ht_irr : Irreducible ts := irreducible_of_ord_one S ts hSt
  obtain ⟨h, hhf, hhw⟩ := _root_.GlobalTheory.Residue.residue_dForm cL cK (m + 1) S ψ hψ hc ts f v w H ht_irr hf (hv ▸ hTK)
    (htv ▸ hzT) (by rw [htv]; exact hH.symm)
  rw [hv] at hhw
  have hne : ∀ {A M : Type} [CommRing A] [Nontrivial A] [AddCommGroup M] [Module A M] {ω : M},
      IsFreeGen A ω → ω ≠ 0 := fun hω h0 => one_ne_zero (hω.1 (a₁ := 1) (a₂ := 0) (by simp [h0]))
  have hIK := _root_.GlobalTheory.FieldPair.formOrd_api cK (m + 1) _ hTK
  have hIL := _root_.GlobalTheory.FieldPair.formOrd_api cL (m + 2) _ hzT
  have hwne := hne (_root_.GlobalTheory.FieldPair.formOrd_api cK (m + 1) _ hw).1
  have hvne := hne hIK.1
  have hΩne : Ω0 ≠ 0 := hne hfreeL
  have hψh : ψ h ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hhw
    exact hwne hhw
  have hh0 : (h : L) ≠ 0 := fun h0 => hψh (by rw [show h = 0 from Subtype.ext h0, map_zero])
  have hf0 : (f : L) ≠ 0 := fun h0 => hf.ne_zero (Subtype.ext h0)
  have ht0 : (t : L) ≠ 0 := fun h0 => ht_irr.ne_zero (Subtype.ext h0)
  have hH0 : H ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hhf
    exact mul_ne_zero hh0 hf0 hhf
  have hFw : F.formOrd (dForm cK (fun i => ψ (w i))) = F.ord (ψ h) := by
    have hs : F.formOrd (ψ h • dForm cK (Fin.cons (ψ us) (fun i => ψ (zs i)))) =
        F.ord (ψ h) + F.formOrd (dForm cK (Fin.cons (ψ us) (fun i => ψ (zs i)))) := by
      simpa only [Place.formOrd] using (hIK.2 F).2.2.1 _ _ hvne hψh
    rw [hhw, hs]
    simpa only [Place.formOrd, hFO, add_zero]
  have hPη : ∀ P : Place cL, P.IsPrimeOf Q → P.formOrd η = P.ord H := by
    intro P hPQ
    have hs : P.formOrd (H • Ω0) = P.ord H + P.formOrd Ω0 := by
      simpa only [Place.formOrd] using (hIL.2 P).2.2.1 Ω0 H hΩne hH0
    rw [← hH, hs]
    simpa only [Place.formOrd, hzO P hPQ, add_zero]
  have hPo : ∀ P : Place cL, P.ord (h : L) + P.ord (f : L) = P.ord H + P.ord (t : L) := by
    intro P
    rw [← P.ord_mul hh0 hf0, ← P.ord_mul hH0 ht0, hhf]
  have hEt : E.ord (t : L) = 0 := (hA2 E hE).resolve_right (by rw [hEu]; norm_num)
  have hSu : S.ord (u : L) = 0 := (hA2 S hS).resolve_left (by rw [hSt]; norm_num)
  have hu0 : (u : L) ≠ 0 := by
    intro h0
    rw [h0] at hEu
    simp [Place.ord] at hEu
  have hE1 := GlobalTheory.T.eq_unit_mul_zpow_regularLocalModel_dimTwo cL Q hQ t u hm hd E hE hEu
  set θ' := Finsupp.mapDomain (fun g : S.ring => (g : L)) θ with hθ'
  have hφs : ∀ g ∈ (Finsupp.single h 1 - θ).support, ψ g ≠ 0 := by
    intro g hg
    rcases Finset.mem_union.1 (Finsupp.support_sub hg) with hg | hg
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hg)]
      exact hψh
    · exact hθ g hg
  have hmc : Finsupp.mapDomain (fun g : S.ring => (g : L)) (Finsupp.single h 1 - θ) =
      Finsupp.single (h : L) 1 - θ' := by
    rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single]
  have hmψ : Finsupp.mapDomain ψ (Finsupp.single h 1 - θ) =
      Finsupp.single (ψ h) 1 - Finsupp.mapDomain ψ θ := by
    rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single]
  have hφP : ∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring →
      P.ordQ (Finsupp.mapDomain (fun g : S.ring => (g : L)) (Finsupp.single h 1 - θ)) = 0 := by
    intro P hPQ hPS hPE
    have h1 := hP P hPQ hPS hPE
    rw [Place.disc, map_add (f := _), Place.ordQ_single, hPη P hPQ] at h1
    have hPt : P.ord (t : L) = 0 := by
      by_contra hne'
      have h0 : 0 ≤ P.ord (t : L) := (P.ord_nonneg_iff ht0).2 (hPQ.1 t t.2)
      exact hPS (hA1 P S hPQ hS (lt_of_le_of_ne h0 (Ne.symm hne')) (by rw [hSt]; norm_num))
    have h2 := hPo P
    rw [hPt, add_zero] at h2
    rw [hmc, map_sub, Place.ordQ_single]
    have h3 : ((P.ord (h : L) : ℤ) : ℚ) = (P.ord H : ℚ) - (P.ord (f : L) : ℚ) := by
      rw [← h2]; push_cast; ring
    rw [h3]
    linarith
  have hE2 := GlobalTheory.T.ordQ_mapDomain_residuePlace_transport cL cK Q u S E ψ F hS.1 hSu hu0 hψ hFr hFu hE1 _ hφs hφP
  rw [hmc, hmψ, map_sub, map_sub, Place.ordQ_single, Place.ordQ_single] at hE2
  refine ⟨F, hFr, ?_⟩
  rw [Place.disc, Place.disc, hFw, map_add (f := _), Place.ordQ_single, hPη E hE]
  have h2 := hPo E
  rw [hEt, add_zero] at h2
  have h3 : ((E.ord H : ℤ) : ℚ) = (E.ord (h : L) : ℚ) + (E.ord (f : L) : ℚ) := by
    rw [← h2]; push_cast; ring
  rw [h3]
  linarith

end GlobalTheory.AdjCodimTwo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorNefAmpleFiniteFieldFibre
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AmpleFibre

theorem isAmpleLB_fibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, NefFib L → IsAmpleLB A.B → ∀ (l : ℕ) [Fact l.Prime], IsAmpleLB ((L.tens A).B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l))))) := by
  intro k _ X _ p D hX L A hL hA l _
  haveI := hX.finite
  have hc := GlobalTheory.NefFibPrime.isClosedImmersion_spMap_zmod l
  haveI : IsClosedImmersion (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l)))) :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip hc
  set f := Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l))) with hf
  set g := Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod l))) with hg
  letI := GlobalTheory.algebraΓOfHom g
  have hproj : IsProjOver g := by
    have h := GlobalTheory.FibreNef.isProjOver_fibre hX.isProjOver l f
    rwa [GlobalTheory.strHom_eq (f := g) fun _ => rfl] at h
  have hN : IsNef (ZMod l) (L.B.pull f) :=
    GlobalTheory.FibreNef.isNef_pull_of_nefOver l f L ((GlobalTheory.VertForm.nefFib_iff L).1 hL l Fact.out)
  have hAf : IsAmpleLB (A.B.pull f) := hA.pull_of_isClosedImmersion f
  have hK := IsAmpleLB.tens_of_isNef GlobalTheory.nefNumerics_outright (ZMod l) _ g hproj _ _ hAf hN
  refine hK.of_lbIso (LB.isLB_pull (L.tens A).isLB f) ?_
  refine (CechPic.cls_eq_iff (LB.isLB_pull (L.tens A).isLB f)
    (CechPic.isLB_tens (LB.isLB_pull A.isLB f) (LB.isLB_pull L.isLB f))).1 ?_
  show CechPic.pull f (CechPic.cls L.B L.isLB + CechPic.cls A.B A.isLB) =
    CechPic.pull f (CechPic.cls A.B A.isLB) + CechPic.pull f (CechPic.cls L.B L.isLB)
  rw [map_add (f := _), add_comm]

end GlobalTheory.AmpleFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageSndOfSubsetSemiAbelianFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.isClosed_image_snd_of_subset_fibre_closedPoint :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G →
      ∀ x : G.left, G.hom x = closedPoint R → IsClosed ({x} : Set G.left) →
      ∀ N : Set (G ⊗ G).left, IsClosed N → N ⊆ (fst G G).left ⁻¹' {x} →
      IsClosed ((snd G G).left '' N) := by
  intro R _ _ G _ hG x hx hxc N hN hNZ
  have hlft : LocallyOfFiniteType G.hom := by
    haveI := hG.smooth; infer_instance
  have hfin : IsFinite (G.left.fromSpecResidueField x ≫ G.hom) :=
    _root_.GlobalTheory.isFinite_fromSpecResidueField_comp_of_isClosed_of_closedPoint R G hlft x hx hxc
  set k := G.left.fromSpecResidueField x
  set f := G.hom
  let i := pullback.snd k (pullback.fst f f)
  have hrange : Set.range i = (pullback.fst f f) ⁻¹' {x} := by
    simp only [i, Scheme.Pullback.range_snd, k, Scheme.range_fromSpecResidueField]
  have hcomp : i ≫ pullback.snd f f =
      (pullbackRightPullbackFstIso f f k).hom ≫ pullback.snd (k ≫ f) f :=
    (pullbackRightPullbackFstIso_hom_snd f f k).symm
  have hcl : IsClosedMap (i ≫ pullback.snd f f) := by
    rw [hcomp]
    haveI := hfin
    haveI : IsFinite (pullback.snd (k ≫ f) f) := inferInstance
    exact ((pullbackRightPullbackFstIso f f k).hom ≫ pullback.snd (k ≫ f) f).isClosedMap
  have hNi : (snd G G).left '' N = (i ≫ pullback.snd f f) '' (i ⁻¹' N) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp, Set.image_preimage_eq_of_subset]
    · rfl
    · rw [hrange]; exact hNZ
  rw [hNi]
  exact hcl _ (hN.preimage i.continuous)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenTransl
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenTransl

variable {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R))

abbrev genOver : Over (Sp R) := Over.mk (pullback.snd G.hom (jK R) ≫ jK R)

def genPr : genOver G ⟶ G := Over.homMk (pullback.fst G.hom (jK R)) pullback.condition

def genPt (a : Over.mk (jK R) ⟶ G) : genOver G ⟶ G :=
  Over.homMk (pullback.snd G.hom (jK R) ≫ a.left) (by
    rw [Category.assoc, Over.w a]; rfl)

def IsGenTransl [GrpObj G] (L L₁ : LB G.left) (a : Over.mk (jK R) ⟶ G) : Prop :=
  LBIso (L₁.pull (pullback.fst G.hom (jK R))) (L.pull ((genPr G * genPt G a).left))

end GlobalTheory.GenTransl
end
end

