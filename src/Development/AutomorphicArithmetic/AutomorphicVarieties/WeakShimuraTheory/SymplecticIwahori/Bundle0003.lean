module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.AdjMulSelf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SmallExt

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.GenTri
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

section Gen

variable {R K H : Type} [CommRing R] [CommRing K] [Group H] (f : R →+* K)

private theorem gt_rep (r : H →* M4 R) (g : H) : mapRep f r g = f.mapMatrix (r g) := rfl

private theorem gt_smul (a : R) (Y : M4 R) : f.mapMatrix (a • Y) = f a • f.mapMatrix Y := by
  ext i j
  simp

private theorem gt_adj (Y : M4 R) : adj (f.mapMatrix Y) = f.mapMatrix (adj Y) := by
  ext i j
  simp only [adj_apply, RingHom.mapMatrix_apply, Matrix.map_apply, map_zsmul]

private theorem gt_gsp {ν : R} {Y : M4 R} (h : IsGSp ν Y) : IsGSp (f ν) (f.mapMatrix Y) := by
  unfold IsGSp at *
  rw [gt_adj, ← map_mul, h, gt_smul, map_one]

private theorem gt_prj (c : Fin 4 → R) (Y : M4 R) (i : Fin 4) :
    prj (fun a => f (c a)) (f.mapMatrix Y) i = f.mapMatrix (prj c Y i) := by
  unfold prj
  have h : ∀ p : R[X], aeval (f.mapMatrix Y) (p.map f) = f.mapMatrix (aeval Y p) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
    | monomial n a =>
      rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, map_mul, map_pow,
        Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, gt_smul, map_one]
  rw [← h, Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

private theorem gt_ord {I : Subgroup H} {ps : Fin 4 → H → R} {s₀ : H} {r : H →* M4 R} (h : Ord I ps s₀ r) :
    Ord I (fun i g => f (ps i g)) s₀ (mapRep f r) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [gt_rep, RingHom.mapMatrix_apply, Matrix.charpoly_map, h.charpoly, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  · intro g i j hij
    rw [gt_rep, gt_rep, gt_prj f (fun a => ps a s₀), gt_prj f (fun a => ps a s₀), ← map_mul, ← map_mul,
      h.stable g i j hij, map_zero]
  · intro s hs i
    rw [gt_rep, gt_rep, gt_prj f (fun a => ps a s₀), ← map_one f.mapMatrix, ← gt_smul, ← map_sub, ← map_mul,
      ← map_mul, h.inert s hs i, map_zero]

private theorem gt_tr (c : Fin 4 → R) (Y Z : M4 R) (i : Fin 4) :
    (prj (fun a => f (c a)) (f.mapMatrix Y) i * f.mapMatrix Z).trace = f (prj c Y i * Z).trace := by
  rw [gt_prj, ← map_mul, RingHom.mapMatrix_apply, AddMonoidHom.map_trace]

private theorem gt_tr_diag (c a : Fin 4 → R) (i : Fin 4) :
    (prj c (Matrix.diagonal c) i * Matrix.diagonal a).trace = (∏ j ∈ Finset.univ.erase i, (c i - c j)) * a i := by
  have h : prj c (Matrix.diagonal c) i = Matrix.diagonal fun b => ∏ j ∈ Finset.univ.erase i, (c b - c j) := by
    unfold prj
    have h1 := aeval_algHom_apply (Matrix.diagonalAlgHom (n := Fin 4) (α := R) R) c
      (∏ j ∈ Finset.univ.erase i, (X - C (c j)))
    rw [Matrix.diagonalAlgHom_apply, Matrix.diagonalAlgHom_apply] at h1
    rw [h1]
    congr 1
    funext b
    simp [map_prod]
  rw [h, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Finset.sum_eq_single i]
  · intro b _ hb
    rw [Finset.prod_eq_zero (i := b) (by simp [hb]) (sub_self _), zero_mul]
  · simp

end Gen

private theorem gt_int {B K : Type} [CommRing B] [Field K] [Algebra B K] (Y : M4 B) {a b : M4 K} (hab : a * b = 1)
    (hM : IsUp (a * (algebraMap B K).mapMatrix Y * b)) (i : Fin 4) :
    IsIntegral B ((a * (algebraMap B K).mapMatrix Y * b) i i) := by
  refine ⟨Y.charpoly, Y.charpoly_monic, ?_⟩
  have e : (a * (algebraMap B K).mapMatrix Y * b).charpoly = ((algebraMap B K).mapMatrix Y).charpoly := by
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, mul_eq_one_comm.1 hab, Matrix.one_mul]
  rw [eval₂_eq_eval_map, ← Matrix.charpoly_map, ← RingHom.mapMatrix_apply, ← e,
    Matrix.charpoly_of_upperTriangular _ (fun i j h => hM i j h), eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

theorem UpperTheory.V.Ws.Pp.genTri :
    ∀ {O B H : Type} [CommRing O] [IsDomain O] [CommRing B] [IsDomain B] [HenselianLocalRing B] [Algebra O B] [Group H] (I : Subgroup H) (ps : Fin 4 → H → O) (s₀ : H) (ν : O) (ρ : H →* M4 B) (x : B →ₐ[O] O), s₀ ∈ I → Function.Injective (fun i => ps i s₀) → (∀ i, ps i s₀ * ps i.rev s₀ = ν) → ν ≠ 0 → IsGSp (algebraMap O B ν) (ρ s₀) → Ord I (fun i g => algebraMap O B (ps i g)) s₀ ρ → (∀ g a b, x (ρ g a b) = Matrix.diagonal (fun i => ps i g) a b) → ∃ (h : M4 (FractionRing B)) (P : H → Fin 4 → B[X]), SpTri (fun g => ρ g) P (algebraMap B (FractionRing B)) h ∧ (∀ g i, ∃ q, Dist (maximalIdeal B) q ∧ P g i = q.comp (X - C (algebraMap O B (ps i g)))) ∧ ∀ s ∈ I, ∀ i, P s i = X - C (algebraMap O B (ps i s)) := by
  intro O B H _ _ _ _ _ _ _ I ps s₀ ν ρ x hs hinj hrev hν hG hρ hx
  have hB : Function.Injective (algebraMap O B) := fun a b e => by simpa using congrArg x e
  have hF := IsFractionRing.injective B (FractionRing B)
  obtain ⟨h, h1, h2, h3, h4⟩ := genFlag I (fun i g => algebraMap B (FractionRing B) (algebraMap O B (ps i g))) s₀
    (algebraMap B (FractionRing B) (algebraMap O B ν)) (mapRep (algebraMap B (FractionRing B)) ρ) hs
    (fun a b e => hinj (hB (hF e))) (fun i => by rw [← map_mul, ← map_mul, hrev])
    ((map_ne_zero_iff _ hF).2 ((map_ne_zero_iff _ hB).2 hν)) (gt_gsp _ hG) (gt_ord _ hρ)
  have key : ∀ g i, ∃ q : B[X], Dist (maximalIdeal B) q ∧
      aeval ((adj h * mapRep (algebraMap B (FractionRing B)) ρ g * h) i i -
        algebraMap B (FractionRing B) (algebraMap O B (ps i g))) q = 0 ∧ (g ∈ I → q = X) := by
    intro g i
    by_cases hg : g ∈ I
    · refine ⟨X, ⟨monic_X, fun n hn => ?_⟩, by rw [h3 g hg, sub_self, aeval_X], fun _ => rfl⟩
      rw [natDegree_X, Nat.lt_one_iff] at hn
      rw [hn, coeff_X_zero]
      exact zero_mem _
    let d : O := ∏ j ∈ Finset.univ.erase i, (ps i s₀ - ps j s₀)
    let t : B := (prj (fun a => algebraMap O B (ps a s₀)) (ρ s₀) i * ρ g).trace
    have hd : d ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 fun e => (Finset.mem_erase.1 hj).1 (hinj e).symm
    have hxt : x t = d * ps i g := by
      have e1 := gt_tr (x : B →+* O) (fun a => algebraMap O B (ps a s₀)) (ρ s₀) (ρ g) i
      have e2 : ∀ g, (x : B →+* O).mapMatrix (ρ g) = Matrix.diagonal fun i => ps i g := fun g => Matrix.ext (hx g)
      simp only [e2, RingHom.coe_coe, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at e1
      rw [gt_tr_diag] at e1
      exact e1.symm
    have hint : IsIntegral B ((adj h * mapRep (algebraMap B (FractionRing B)) ρ g * h) i i) :=
      gt_int (ρ g) (adj_mul_self h1) (h2 g) i
    have hk : algebraMap B (FractionRing B) (algebraMap O B d) *
        (adj h * mapRep (algebraMap B (FractionRing B)) ρ g * h) i i = algebraMap B _ t := by
      rw [← gt_tr (algebraMap B (FractionRing B)), map_prod, map_prod]
      simp only [map_sub]
      exact h4 i g
    obtain ⟨q, hq, h0⟩ := nearPoly x d (t - algebraMap O B (d * ps i g))
      ((adj h * mapRep (algebraMap B (FractionRing B)) ρ g * h) i i - algebraMap B _ (algebraMap O B (ps i g))) hd
      (by rw [map_sub, hxt, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self])
      (hint.sub isIntegral_algebraMap) (by rw [mul_sub, hk, map_sub, map_mul, map_mul])
    exact ⟨q, hq, h0, fun e => absurd e hg⟩
  choose q hq h0 hI using key
  refine ⟨h, fun g i => (q g i).comp (X - C (algebraMap O B (ps i g))), ⟨h1, fun g => ⟨h2 g, fun i => ?_⟩⟩,
    fun g i => ⟨_, hq g i, rfl⟩, fun s hs i => by simp only [hI s i hs, X_comp]⟩
  rw [← aeval_def, aeval_comp, map_sub, aeval_X, aeval_C]
  exact h0 g i
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.SmallFlag
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

theorem UpperTheory.V.Ws.Pp.smallFlag :
    ∀ {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) {Γ : Type} [Group Γ] [TopologicalSpace Γ] (r : Γ →* M4 𝔞.V) (u : M4 𝔞.V), 𝔞.Small (⟨r, fun _ => 1⟩ : PD Unit _ _) → 𝔞.Small (⟨r, fun _ => u⟩ : PD Unit _ _) := by
  classical
  intro l _ 𝔞 Γ _ _ r u hS
  unfold Amb.Small at hS ⊢
  obtain ⟨A, _, _, _, f, P₁, hf, hc, hP⟩ := hS
  obtain ⟨A', _, _, _, f', g, hf', hcomp, hcl⟩ :=
    smallExt 𝔞 A f hf (Finset.univ.image (fun ij : Fin 4 × Fin 4 => 𝔞.toK (u ij.1 ij.2)))
  have hinj : Function.Injective f' := hf'.inj
  have hloc : IsLocalHom g := by
    have := Amb.IsDvr.loc hf
    refine ⟨fun z hz => isUnit_of_map_unit f z ?_⟩
    rw [← hcomp]
    exact hz.map f'
  have hle : (maximalIdeal A).map g ≤ maximalIdeal A' := by
    rw [Ideal.map_le_iff_le_comap]
    intro z hz
    simp only [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff] at hz ⊢
    exact fun h => hz (isUnit_of_map_unit g z h)
  have huR : ∀ i j, u i j ∈ f'.range := fun i j =>
    hcl _ (Subfield.subset_closure (Or.inr
      (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ (i, j))))))
  let e : 𝔞.V → A' := Function.invFun f'
  have hE : ∀ i j, f' (e (u i j)) = u i j := fun i j => by
    obtain ⟨y, hy⟩ := huR i j
    exact Function.invFun_eq ⟨y, hy⟩
  have hr : ∀ γ i j, f (P₁.r γ i j) = r γ i j := fun γ i j =>
    congrArg (fun P => PD.r P γ i j) hP
  refine ⟨A', inferInstance, inferInstance, inferInstance, f',
    ⟨(P₁.map g).r, fun _ => u.map e⟩, hf', ?_, ?_⟩
  · unfold PD.Cont
    intro i j N
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hA := (IsLocallyConstant.iff_eventually_eq _).1 (hc i j N) x
    filter_upwards [hA] with y hy
    rw [Ideal.Quotient.eq] at hy ⊢
    change g (P₁.r y i j) - g (P₁.r x i j) ∈ _
    rw [← map_sub]
    have h2 := Ideal.mem_map_of_mem g hy
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono hle _ h2
  · apply PD.ext
    · ext γ i j
      change ((f' (g (P₁.r γ i j)) : 𝔞.K)) = (r γ i j : 𝔞.K)
      rw [← RingHom.comp_apply f' g, hcomp, hr]
    · ext v i j
      exact congrArg Subtype.val (hE i j)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.TriIwa
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

private theorem adj_mul {R : Type} [CommRing R] (X Y : M4 R) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private theorem adj_adj {R : Type} [CommRing R] (X : M4 R) : adj (adj X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

theorem UpperTheory.V.Ws.Pp.triIwa :
    ∀ {ι A F : Type} [CommRing A] [Field F] (V : ValuationSubring F) (M : ι → M4 A) (P : ι → Fin 4 → A[X]) (g : A →+* V) (h : M4 F), SpTri M P (V.subtype.comp g) h → ∃ k : M4 V, SpTri M P g k := by
  intro ι A F _ _ V M P g h hh
  obtain ⟨k, hk, hb⟩ := spIwa V h hh.1
  refine ⟨k, SpTri.of_map V.subtype Subtype.val_injective ?_⟩
  have a : adj (k.map V.subtype) = (adj k).map V.subtype := by
    ext i j
    simp only [adj_apply, Matrix.map_apply, map_zsmul]
  have k1 : adj (k.map V.subtype) * k.map V.subtype = 1 := by
    rw [a, ← Matrix.map_mul, adj_mul_self hk, Matrix.map_one _ (map_zero _) (map_one _)]
  generalize k.map V.subtype = K at hb k1
  have h2 : h * adj h = 1 := mul_adj_self hh.1
  have hb' : IsUp (adj h * K) := by
    have := IsUp_adj hb
    rwa [adj_mul, adj_adj] at this
  have one : adj K * h * (adj h * K) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc h, h2, Matrix.one_mul, k1]
  refine ⟨k1.trans (one_smul _ _).symm, fun i => ?_⟩
  have e : ∀ X : M4 F, adj K * X * K = adj K * h * (adj h * X * h) * (adj h * K) := fun X => by
    calc adj K * X * K = adj K * (h * adj h) * X * (h * adj h) * K := by
          rw [h2, Matrix.mul_one, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have c := upConj one hb hb' (hh.2 i).1
  rw [e]
  exact ⟨c.1, fun j => by rw [c.2 j]; exact (hh.2 i).2 j⟩
end

