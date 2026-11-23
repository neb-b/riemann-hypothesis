module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.TrPoly
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.EigChp
section
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem eig_dvd {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (F : O) (hF : F ≠ 0) :
    ∃ K : ℕ, ∀ b : O, b - F ∈ maximalIdeal O ^ K → b ∣ F := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨v, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hF hp
  refine ⟨v + 1, fun b hb => ?_⟩
  rw [hp.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hb
  obtain ⟨c, hc⟩ := hb
  have hun : IsUnit ((u : O) + p * c) := by
    by_contra hn
    have h1 : (u : O) + p * c ∈ maximalIdeal O := hn
    have h2 : p * c ∈ maximalIdeal O := Ideal.mul_mem_right _ _ hp.not_isUnit
    have h3 : (u : O) ∈ maximalIdeal O := by simpa using Ideal.sub_mem _ h1 h2
    exact h3 u.isUnit
  have hb' : b = ((u : O) + p * c) * p ^ v := by
    rw [sub_eq_iff_eq_add] at hc
    rw [hc, hu]; ring
  rw [hb', hu, hun.mul_left_dvd]
  exact Dvd.intro_left _ rfl

private theorem eig_fEl {O : Type} [CommRing O] (I : Ideal O) {q n : ℕ} (Nq : Fin q → ℕ)
    (hN : ∀ j, (Nq j : O) - 1 ∈ I) (a b : Fin q → Fin n → O) (h : ∀ j i, a j i - b j i ∈ I) :
    fEl Nq a - fEl (fun _ => 1) b ∈ I := by
  rw [← Ideal.Quotient.eq]
  have h1 : ∀ j, Ideal.Quotient.mk I (Nq j : O) = 1 := fun j => by
    rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact hN j
  have h2 : ∀ j i, Ideal.Quotient.mk I (a j i) = Ideal.Quotient.mk I (b j i) := fun j i =>
    Ideal.Quotient.eq.2 (h j i)
  simp only [fEl, map_prod, map_mul, map_sub, h1, h2, Nat.cast_one, map_one]

private theorem eig_chp {O : Type} [CommRing O] (I : Ideal O) {n : ℕ} (A B : Matrix (Fin n) (Fin n) O)
    (h : ∀ a b, A a b - B a b ∈ I) (k : ℕ) : A.charpoly.coeff k - B.charpoly.coeff k ∈ I := by
  rw [← Ideal.Quotient.eq, ← Polynomial.coeff_map, ← Polynomial.coeff_map, ← Matrix.charpoly_map,
    ← Matrix.charpoly_map]
  have hAB : A.map (Ideal.Quotient.mk I) = B.map (Ideal.Quotient.mk I) := by
    ext a b
    exact Ideal.Quotient.eq.2 (h a b)
  rw [hAB]

theorem UpperTheory.V.Th.Sp.eig :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (y : Pt G0.frame O n) (al : Fin T.q → Fin n → O), (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1) → Th.Eig y T al → ∃ F : O, F ≠ 0 ∧ ∀ᶠ N in atTop, ∃ α : Fin T.q → Fin n → O, (∀ j, (mat y.ρ ((T.h N).p₀ (T.ph N j))).charpoly = ∏ i, (Polynomial.X - Polynomial.C (α j i))) ∧ fEl (T.Nq N) α ∣ F := by
  intro l _ L G0 T n O _ _ _ hc _ y al hP hE
  haveI : IsAdicComplete (maximalIdeal O) O := hc.complete
  have hF : fEl (fun _ => 1) al ≠ 0 := by
    simp only [fEl, Nat.cast_one, one_mul]
    refine Finset.prod_ne_zero_iff.2 fun j _ => Finset.prod_ne_zero_iff.2 fun i _ =>
      Finset.prod_ne_zero_iff.2 fun i' hi' => ?_
    have hne : al j i - al j i' ≠ 0 := fun h0 =>
      (Finset.ne_of_mem_erase hi') ((hE j).1 (sub_eq_zero.1 h0)).symm
    exact mul_ne_zero hne hne
  obtain ⟨K, hK⟩ := eig_dvd _ hF
  refine ⟨_, hF, ?_⟩
  choose K' hK' using fun j => UpperTheory.V.Th.Sp.hens O n (al j) (hE j).1 K
  have hlO : (l : O) ∈ maximalIdeal O := by
    haveI : CharP (ResidueField O) l := hc.char
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  filter_upwards [UpperTheory.V.Th.Sp.close l L G0 T n O y hP (Finset.univ.sup K'), eventually_ge_atTop K] with N hN hNK
  have key : ∀ j, ∃ α : Fin n → O, (mat y.ρ ((T.h N).p₀ (T.ph N j))).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C (α i)) ∧ ∀ i, α i - al j i ∈ maximalIdeal O ^ K := by
    intro j
    refine hK' j _ (Matrix.charpoly_monic _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]) fun k => ?_
    rw [← (hE j).2]
    exact Ideal.pow_le_pow_right (Finset.le_sup (f := K') (Finset.mem_univ j)) (eig_chp _ _ _ (hN j) k)
  choose α h1 h2 using key
  refine ⟨α, h1, hK _ (eig_fEl _ _ (fun j => ?_) _ _ h2)⟩
  obtain ⟨c, hc'⟩ := (T.Nq_mod N j).symm.dvd
  have h3 : (T.Nq N j : O) - 1 = (l : O) ^ N * (c : O) := by
    have := congrArg (Int.cast : ℤ → O) hc'
    simpa using this
  rw [h3]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right hNK (Ideal.pow_mem_pow hlO N))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.ImportsTer
section
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.kill :
    ∀ (O R B M V : Type) [CommRing O] [CommRing R] [CommRing B] [Algebra O R] [Algebra O B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] (q n : ℕ) (β : R →ₐ[O] B) (x : B →ₐ[O] O) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (f : PU R q n) (α : Fin q → Fin n → O) (I : Ideal R) (t₀ : R), Function.Surjective β → TwoMaps (M := M) β.toRingHom P act f → (∀ j, (P j).map (x : B →+* O) = ∏ i, (Polynomial.X - Polynomial.C (α j i))) → (∀ a : B, x a = 0 → ∀ m : M, (β t₀ * a) • m ∈ (I.map β • ⊤ : Submodule B M)) → ∀ a : PU R q n, MvPolynomial.eval₂ ((x.comp β : R →ₐ[O] O) : R →+* O) (fun p => α p.1 p.2) a = 0 → ∀ v : V, act (MvPolynomial.C t₀ * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k)))) * f * a) v ∈ (I • ⊤ : Submodule R V) := by
  intro O R B M V _ _ _ _ _ _ _ _ _ q n β x P act f α I t₀ hβ hTM hP hker a ha v
  obtain ⟨φ, ψ, h1, h2, h3, h4⟩ := hTM
  have hπC : ∀ b : B, (Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.C b) =
      algebraMap B (MSplitAlg P n) b := fun b => rfl
  have key : ∀ i ∈ I, ∀ w : MSplitAlg P n ⊗[B] M, φ ((β i) • w) ∈ (I • ⊤ : Submodule R V) := by
    intro i hi w
    have e1 : (β i) • w = (Ideal.Quotient.mk (mSplitIdeal P n))
        ((MvPolynomial.map β.toRingHom) (MvPolynomial.C i)) • w := by
      rw [MvPolynomial.map_C, hπC, algebraMap_smul]
      rfl
    rw [e1, h1, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Module.algebraMap_end_apply]
    exact Submodule.smul_mem_smul hi trivial
  have claim : ∀ b : B, x b = 0 → ∀ z : MSplitAlg P n ⊗[B] M,
      φ (algebraMap B (MSplitAlg P n) (β t₀ * b) • z) ∈ (I • ⊤ : Submodule R V) := by
    intro b hb z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
      rw [algebraMap_smul, ← TensorProduct.tmul_smul]
      refine Submodule.smul_induction_on (p := fun y => φ (s ⊗ₜ[B] y) ∈ (I • ⊤ : Submodule R V))
        (hker b hb m) ?_ ?_
      · intro r hr m' _
        obtain ⟨i, hi, rfl⟩ := (Ideal.mem_map_iff_of_surjective β hβ).mp hr
        rw [TensorProduct.tmul_smul]
        exact key i hi _
      · intro y1 y2 k1 k2
        rw [TensorProduct.tmul_add, map_add (f := _)]
        exact add_mem k1 k2
    | add z1 z2 k1 k2 =>
      rw [smul_add, map_add (f := _)]
      exact add_mem k1 k2
  have gen : ∀ y ∈ Ideal.map (algebraMap B (MSplitAlg P n)) (RingHom.ker x), ∀ z : MSplitAlg P n ⊗[B] M,
      φ ((algebraMap B (MSplitAlg P n) (β t₀) * y) • z) ∈ (I • ⊤ : Submodule R V) := by
    intro y hy
    unfold Ideal.map at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      intro z
      rw [← map_mul]
      exact claim b (RingHom.mem_ker.mp hb) z
    | zero => intro z; simp
    | add y1 y2 _ _ k1 k2 =>
      intro z
      rw [mul_add, add_smul, map_add (f := _)]
      exact add_mem (k1 z) (k2 z)
    | smul r y _ k =>
      intro z
      rw [smul_eq_mul, mul_left_comm, mul_comm r, mul_smul]
      exact k _
  have hE : MvPolynomial.map β.toRingHom (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
      (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k))) : PU R q n) =
      ∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
      (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k))) := by
    simp [map_prod]
  have hmem := Sp.msp O B (Fin q) n x P α hP (MvPolynomial.map β.toRingHom a)
    (by rw [MvPolynomial.eval₂_map]; exact ha)
  have e3 : act (MvPolynomial.C t₀ * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
      (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k)))) * f * a) v =
      φ (((Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.map β.toRingHom (MvPolynomial.C t₀ *
        (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k)))))) *
        (Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.map β.toRingHom a)) • ψ v) := by
    rw [mul_smul, ← h2, h1, h3]
    simp only [map_mul, Module.End.mul_apply]
  rw [e3]
  have e4 : (Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.map β.toRingHom (MvPolynomial.C t₀ *
        (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k)))))) *
        (Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.map β.toRingHom a) =
      algebraMap B (MSplitAlg P n) (β t₀) * (Ideal.Quotient.mk (mSplitIdeal P n))
        ((∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k)))) *
          MvPolynomial.map β.toRingHom a) := by
    rw [map_mul (MvPolynomial.map β.toRingHom), hE, MvPolynomial.map_C, ← hπC, ← map_mul, ← map_mul,
      mul_assoc]
    rfl
  rw [e4]
  exact gen _ hmem _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.RepSingle
section
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem tr_map {R S G : Type} [CommRing R] [CommRing S] [Group G] {n : ℕ} (D : GDet n R G)
    (f : R →+* S) (z : MonoidAlgebra R G) :
    (D.map f).tr (MonoidAlgebra.mapRingHom G f z) = f (D.tr z) :=
  ((UpperTheory.V.CA.d_gmap D).2.2.1 f z).2 1

private theorem tr_rep {R G : Type} [CommRing R] [Group G] {n : ℕ} (hn : 1 ≤ n) (ρ : G →* Matrix (Fin n) (Fin n) R)
    (z : MonoidAlgebra R G) : (GDet.ofRep ρ).tr z = (GDet.repAlg ρ R z).trace := by
  have h : (GDet.ofRep ρ).chi z = (GDet.repAlg ρ R z).charpoly := by
    change (GDet.repAlg ρ (Polynomial R) _).det = Matrix.det _
    congr 1
    rw [map_sub, Matrix.charmatrix]
    congr 1
    · ext i j : 2
      simp [GDet.repAlg, Matrix.one_apply, Matrix.diagonal_apply]
    · induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | single g r => ext i j : 2; simp [GDet.repAlg]
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [GDet.tr, GDet.lam, h, Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]
  simp

private theorem rep_single {R G : Type} [CommRing R] [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) R) (g : G) (a : R) :
    GDet.repAlg ρ R (MonoidAlgebra.single g a) = a • ρ g := by
  ext i j; simp [GDet.repAlg]

private theorem rep_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (φ : H →* G) :
    (GDet.ofRep ρ).comap φ = GDet.ofRep (ρ.comp φ) := by
  refine GDet.ext fun B _ _ x => ?_
  change (GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B φ x)).det = (GDet.repAlg (ρ.comp φ) B x).det
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g r => simp [GDet.repAlg]

private noncomputable def qq {R G : Type} [CommRing R] [Group G] {n : ℕ} (E : ℕ) (ph : G) (u : Fin n → R) (i : Fin n) :
    MonoidAlgebra R G :=
  (List.ofFn fun k => if k = i then 1 else MonoidAlgebra.single ph (1 : R) - MonoidAlgebra.single 1 (u k)).prod ^ (E + 1)

private theorem qq_map {R S G : Type} [CommRing R] [CommRing S] [Group G] {n : ℕ} (f : R →+* S) (E : ℕ) (ph : G)
    (u : Fin n → R) (i : Fin n) :
    MonoidAlgebra.mapRingHom G f (qq E ph u i) = qq E ph (fun k => f (u k)) i := by
  simp [qq, map_list_prod, List.map_ofFn, Function.comp_def, apply_ite (MonoidAlgebra.mapRingHom G f)]

private theorem qq_tr {O G : Type} [CommRing O] [IsDomain O] [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) O) (E : ℕ) (ph : G)
    (α : Fin n → O) (i : Fin n) (h : (ρ ph).charpoly = ∏ k, (Polynomial.X - Polynomial.C (α k))) :
    (GDet.ofRep ρ).tr (qq E ph α i) = (∏ k ∈ Finset.univ.erase i, (α i - α k)) ^ (E + 1) := by
  have e : GDet.repAlg ρ O (qq E ph α i) = Polynomial.aeval (ρ ph)
      ((∏ k, if k = i then 1 else (Polynomial.X - Polynomial.C (α k))) ^ (E + 1)) := by
    rw [qq, map_pow, map_pow, ← List.prod_ofFn, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    congr 3
    funext k
    by_cases hk : k = i <;> simp [hk, rep_single, Algebra.algebraMap_eq_smul_one]
  rw [tr_rep (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) i.2)), e, Sp.trp O n _ α _ h,
    Finset.sum_eq_single i]
  · rw [Polynomial.eval_pow, Polynomial.eval_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), if_pos rfl,
      Polynomial.eval_one, mul_one]
    congr 1
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [if_neg (Finset.mem_erase.1 hk).1]
    simp
  · intro a _ ha
    rw [Polynomial.eval_pow, Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ a) (by simp [ha]), zero_pow E.succ_ne_zero]
  · exact fun h => (h (Finset.mem_univ _)).elim

private theorem core {O R T G X : Type} [CommRing O] [IsDomain O] [CommRing R] [CommRing T] [Algebra O R] [Algebra O T] [Group G]
    [AddCommGroup X] [Module O X] {n : ℕ} (D : GDet n R G) (c : R →+* T) (hc : ∀ a, c (algebraMap O R a) = algebraMap O T a)
    (x : T →ₐ[O] O) (del : T →ₗ[O] X) (ρ : G →* Matrix (Fin n) (Fin n) O) (hD : D.map ((x : T →+* O).comp c) = GDet.ofRep ρ)
    (ph ta : G) (α : Fin n → O) (E : ℕ) (i : Fin n) (u : Fin n → T) (y : T) (hn : 1 ≤ n) (hta : ρ ta = 1)
    (h : (ρ ph).charpoly = ∏ k, (Polynomial.X - Polynomial.C (α k))) (hu : ∀ k, x (u k) = α k) (hy : x y = 0)
    (hd : IsDer x del) :
    x ((D.map c).tr (twoPowerModulus E ph ta u i y)) = 0 ∧ del ((D.map c).tr (twoPowerModulus E ph ta u i y)) =
      del (c (D.tr (twoPowerModulus E ph ta (fun k => algebraMap O R (α k)) i 0))) -
        (∏ k ∈ Finset.univ.erase i, (α i - α k)) ^ (E + 1) • del y := by
  have hx : ∀ z, x ((D.map c).tr z) = (GDet.ofRep ρ).tr (MonoidAlgebra.mapRingHom G (x : T →+* O) z) := fun z => by
    rw [← hD, ← (UpperTheory.V.CA.d_gmap D).2.1 c (x : T →+* O), tr_map]
    rfl
  obtain ⟨k1, k2⟩ := Sp.q2 O T G X n (D.map c) x del ta y (qq E ph u i) hn hd hy fun g => by
    rw [hx, hx, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapRingHom_single, tr_rep hn, tr_rep hn, rep_single, rep_single,
      map_mul, hta, mul_one]
  refine ⟨k1, k2.trans ?_⟩
  have e1 : (fun k => (x : T →+* O) (u k)) = α := funext hu
  have e2 : MonoidAlgebra.mapRingHom G c (twoPowerModulus E ph ta (fun k => algebraMap O R (α k)) i 0) =
      MonoidAlgebra.mapRingHom G ((algebraMap O T).comp (x : T →+* O)) (qq E ph u i) *
        (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 0) := by
    change MonoidAlgebra.mapRingHom G c (qq E ph _ i * _) = _
    rw [map_mul, qq_map, qq_map]
    congr 1
    · congr 1
      funext k
      rw [hc, ← hu k]
      rfl
    · simp
  rw [← e2, tr_map, hx, qq_map, e1, qq_tr ρ E ph α i h]

theorem UpperTheory.V.Th.Sp.q2op :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 G : Glob l L) (h : G.Hom G0) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (q N : ℕ) (A : OpMod b h q N) (y : Pt G0.frame O n) (x : B →ₐ[O] O) (ph ta : G.G₀) (α : Fin n → O) (E : ℕ) (j : Fin q) (i : Fin n) (xT : PUY A.R q n →ₐ[O] O) (X : Type) [AddCommGroup X] [Module O X] (del : PUY A.R q n →ₗ[O] X), 1 ≤ n → u.Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ → h.p₀ ta = 1 → (mat y.ρ (h.p₀ ph)).charpoly = ∏ k, (Polynomial.X - Polynomial.C (α k)) → (∀ s, xT (MvPolynomial.C s) = x (A.β s)) → (∀ k, xT (uV A.R j k) = α k) → xT (yV A.R j i) = 0 → IsDer xT del → xT ((A.p.D.map (MvPolynomial.C : A.R →+* PUY A.R q n)).tr (twoPowerModulus E ph ta (uV A.R j) i (yV A.R j i))) = 0 ∧ del ((A.p.D.map (MvPolynomial.C : A.R →+* PUY A.R q n)).tr (twoPowerModulus E ph ta (uV A.R j) i (yV A.R j i))) = del (MvPolynomial.C (A.p.D.tr (twoPowerModulus E ph ta (fun k => algebraMap O A.R (α k)) i 0))) - (∏ k ∈ Finset.univ.erase i, (α i - α k)) ^ (E + 1) • del (yV A.R j i) := by
  intro l _ L G0 G h n O _ _ _ _ _ r B _ _ _ u J D b q N A y x ph ta α E j i xT X _ _ del hn hmap hta hα hC hu hy hd
  refine core (O := O) (T := PUY A.R q n) A.p.D MvPolynomial.C (fun a => rfl) xT del ((mat y.ρ).comp h.p₀) ?_ ph ta α E i _ _ hn ?_ hα hu hy hd
  · have e : (xT : PUY A.R q n →+* O).comp MvPolynomial.C = x.toRingHom.comp A.β.toRingHom := RingHom.ext hC
    rw [e, ← (UpperTheory.V.CA.d_gmap A.p.D).2.1, A.β_pair.1, ← rep_comap, ← hmap.1]
    rfl
  · rw [MonoidHom.comp_apply, hta, map_one]
end

