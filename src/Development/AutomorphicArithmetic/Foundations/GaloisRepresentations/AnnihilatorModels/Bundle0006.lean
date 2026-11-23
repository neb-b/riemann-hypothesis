module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNilEmb
section
noncomputable section

open TensorProduct Module

namespace UpperTheory.Gal.crystallineComparison

section Comm
variable {L M N : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup N] [Module L N]

private theorem pow_comm (φ : M →ₗ[L] N) (A : End L M) (A' : End L N) (h : ∀ y, φ (A y) = A' (φ y)) (n : ℕ) (y : M) :
    φ ((A ^ n) y) = (A' ^ n) (φ y) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

private theorem aeval_comm (φ : M →ₗ[L] N) (A : End L M) (A' : End L N) (h : ∀ y, φ (A y) = A' (φ y)) (Q : Polynomial L) (y : M) :
    φ (Polynomial.aeval A Q y) = Polynomial.aeval A' Q (φ y) :=
  _root_.UpperTheory.Reformulated.B.Qk66.aeval_comm φ A A' h Q y

end Comm

section
variable {F G B : Type} [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B)
  {L : Type} [Field L] [Algebra F L] {V W : Type} [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
  [AddCommGroup W] [Module L W] [Module F W] [IsScalarTower F L W]

private def ext1 (B : Type) [AddCommGroup B] [Module F B] (f : V →ₗ[L] W) : V ⊗[F] B →ₗ[L] W ⊗[F] B :=
  AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B)

private theorem scalar_extension_tmul (f : V →ₗ[L] W) (v : V) (b : B) : ext1 (F := F) B f (v ⊗ₜ b) = f v ⊗ₜ b := by
  simp [ext1]

private theorem typeCharacterExtension_mem_range_coefficientRing {ρ : Representation L G V} {ρ' : Representation L G W} {f : V →ₗ[L] W} (h : Inter ρ ρ' f)
    {x : V ⊗[F] B} (hx : x ∈ Dinv σ ρ) : ext1 B f x ∈ Dinv σ ρ' := by
  rw [mem_Dinv] at hx ⊢
  intro g
  have key : ∀ y : V ⊗[F] B, AlgebraTensorModule.map (ρ' g) (σ g) (ext1 B f y) =
      ext1 B f (AlgebraTensorModule.map (ρ g) (σ g) y) := by
    intro y
    induction y with
    | tmul v b => simp [scalar_extension_tmul, h g v]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [key, hx]

private theorem scalar_extension_period_action (f : V →ₗ[L] W) (y : V ⊗[F] B) :
    ext1 B f (onPer ψ L V y) = onPer ψ L W (ext1 B f y) := by
  induction y with
  | tmul v b => simp [scalar_extension_tmul, onPer]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

private theorem scalar_extension_basis_coord {κ : Type} [DecidableEq κ] (b : Basis κ F B) (f : V →ₗ[L] W) (y : V ⊗[F] B) (k : κ) :
    TensorProduct.equivFinsuppOfBasisRight b (ext1 B f y) k = f (TensorProduct.equivFinsuppOfBasisRight b y k) := by
  induction y with
  | tmul v c =>
    rw [scalar_extension_tmul, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
      TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, LinearMap.map_smul_of_tower]
  | add a c ha hc => simp only [map_add (f := _), Finsupp.add_apply, ha, hc]

end

theorem nilEmb_of : NilEmb := by
  intro F G B _ _ _ _ σ ψ L _ _ V _ _ _ _ ρ I _ W _ _ _ _ ρ' f hI hinj Q hQ
  classical
  cases nonempty_fintype I
  choose N hN using hQ
  refine ⟨∑ i, N i, fun x hx => ?_⟩
  set A := Polynomial.aeval (onPer ψ L V) Q with hA
  have hzero : ∀ i, ext1 B (f i) ((A ^ ∑ i, N i) x) = 0 := by
    intro i
    have hle : N i ≤ ∑ i, N i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [pow_comm (ext1 B (f i)) A (Polynomial.aeval (onPer ψ L (W i)) Q)
      (aeval_comm _ _ _ (scalar_extension_period_action ψ (f i)) Q), ← Nat.sub_add_cancel hle, pow_add, Module.End.mul_apply,
      hN i _ (typeCharacterExtension_mem_range_coefficientRing σ (hI i) hx), map_zero]
  apply (TensorProduct.equivFinsuppOfBasisRight (Basis.ofVectorSpace F B)).injective
  ext k
  rw [map_zero, Finsupp.zero_apply]
  refine hinj _ fun i => ?_
  rw [← scalar_extension_basis_coord, hzero i, map_zero, Finsupp.zero_apply]

end UpperTheory.Gal.crystallineComparison
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNormEx
section
noncomputable section

namespace UpperTheory.Gal.crystallineComparison

theorem normEx_of : MatRep → DetSplit → NormEx := by
  intro hMR hDS R S _ _ _ _ _ ι _ s
  obtain ⟨m, M, hM⟩ := hMR R S
  let φ : R →+* Polynomial (MvPolynomial ι R) := Polynomial.C.comp MvPolynomial.C
  refine ⟨(1 - (M 1).map φ + (Polynomial.X : Polynomial (MvPolynomial ι R)) • (M 1).map φ
    - ∑ k, (Polynomial.C (MvPolynomial.X (R := R) k) : Polynomial (MvPolynomial ι R)) • (M (s k)).map φ).det, ?_⟩
  intro B _ _ I _ z hz
  classical
  obtain ⟨P, Q, hPQ, hQ⟩ := hM B I z hz
  let ψ : B →+* Polynomial (MvPolynomial ι B) := Polynomial.C.comp MvPolynomial.C
  let F : Polynomial (MvPolynomial ι R) →+* Polynomial (MvPolynomial ι B) :=
    Polynomial.mapRingHom (MvPolynomial.map (algebraMap R B))
  have hPQ' : P.map ψ * Q.map ψ = 1 := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_one ψ (map_zero _) (map_one _)]
  have key := hDS (Polynomial (MvPolynomial ι B)) m I (P.map ψ) (Q.map ψ) hPQ'
    (fun i => form fun k => z i (s k))
  rw [← key]
  have hmap : ∀ t : S, ((M t).map φ).map F = Q.map ψ * (Matrix.diagonal fun i => z i t).map ψ * P.map ψ := by
    intro t
    have : ((M t).map φ).map F = ((M t).map (algebraMap R B)).map ψ := by
      rw [Matrix.map_map, Matrix.map_map]
      congr 1
      funext r
      simp [φ, ψ, F]
    rw [this, hQ t, Matrix.map_mul, Matrix.map_mul]
  have hd : Matrix.diagonal (fun i => form fun k => z i (s k))
      = (Polynomial.X : Polynomial (MvPolynomial ι B)) • (1 : Matrix I I _)
        - ∑ k, (Polynomial.C (MvPolynomial.X (R := B) k) : Polynomial (MvPolynomial ι B))
          • (Matrix.diagonal fun i => z i (s k)).map ψ := by
    ext i j
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply]
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with h
    · subst h
      set_option synthInstance.maxHeartbeats 100000 in
        simp [form, ψ, map_sum, mul_comm]
    · simp
  have hs : ∀ (c : Polynomial (MvPolynomial ι R)) (A : Matrix (Fin m) (Fin m) (Polynomial (MvPolynomial ι R))),
      F.mapMatrix (c • A) = F c • F.mapMatrix A := by
    intro c A
    ext i j
    simp
  have h1 : (Matrix.diagonal fun i => z i 1).map ψ = 1 := by
    simp
  change F _ = _
  rw [RingHom.map_det]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_add (f := _), map_sub, map_one, map_sum]
  simp only [hs, RingHom.mapMatrix_apply, hmap, h1, Matrix.mul_one]
  rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_sum,
    Matrix.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  simp [F]
  abel

end UpperTheory.Gal.crystallineComparison
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNormInt
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.normInt_of :
    NormEx → SplitsBC → InjSplit → CoeffInt → LiftP → NormInt := by
  intro hNE hBC hIS hCI hLP l d R S _ _ _ h hcl ι _ s
  haveI hfin : Module.Finite R S := h.fin
  haveI het := h.et
  haveI : Module.Finite (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) := inferInstance
  haveI : Algebra.FinitePresentation (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) := inferInstance
  haveI : Module.FinitePresentation (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ _
  haveI : Module.Flat (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) := inferInstance
  haveI : Module.Projective (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) :=
    Module.Flat.projective_of_finitePresentation
  obtain ⟨N', hN'⟩ := hNE (Localization.Away (l : R)) (Localization.Away (l : R) ⊗[R] S) ι (fun k => 1 ⊗ₜ s k)
  obtain ⟨T, _, _, m, z, hinj, hz⟩ := hIS l d R S h
  haveI : FaithfulSMul (Localization.Away (l : R)) T :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  letI : Algebra R T := ((algebraMap (Localization.Away (l : R)) T).comp (algebraMap R (Localization.Away (l : R)))).toAlgebra
  haveI : IsScalarTower R (Localization.Away (l : R)) T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hNz := hN' T (Fin m) z hz
  have hint : ∀ i k, IsIntegral R (z i (1 ⊗ₜ s k)) := by
    intro i k
    have hs : IsIntegral R (s k) := Algebra.IsIntegral.isIntegral (R := R) (s k)
    have := hs.map (((z i).restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : S →ₐ[R] (Localization.Away (l : R) ⊗[R] S)))
    simpa using this
  have hco : ∀ (a : ℕ) (mm : ι →₀ ℕ), ∃ r, algebraMap R (Localization.Away (l : R)) r = AddMonoidAlgebra.coeff (N'.coeff a) mm := by
    intro a mm
    apply hcl
    have h1 := hCI R T ι (Fin m) (fun i k => z i (1 ⊗ₜ s k)) hint a mm
    rw [← hNz, Polynomial.coeff_map, MvPolynomial.coeff_map] at h1
    exact (isIntegral_algebraMap_iff ).1 h1
  obtain ⟨N, hN⟩ := hLP R (Localization.Away (l : R)) ι (algebraMap R (Localization.Away (l : R))) N' hco
  refine ⟨N, ?_⟩
  intro B _ _ hl I _ zB hzB
  letI : Algebra (Localization.Away (l : R)) B :=
    (IsLocalization.Away.lift (S := Localization.Away (l : R)) (l : R) (g := algebraMap R B) (by simpa using hl)).toAlgebra
  haveI : IsScalarTower R (Localization.Away (l : R)) B := IsScalarTower.of_algebraMap_eq fun r =>
    (IsLocalization.Away.lift_eq (S := Localization.Away (l : R)) (l : R) (g := algebraMap R B) (by simpa using hl) r).symm
  obtain ⟨z', hz', hzz⟩ := hBC R (Localization.Away (l : R)) S B I zB hzB
  have h2 := hN' B I z' hz'
  simp only [hzz] at h2
  rw [← h2, ← hN]
  have hc : (MvPolynomial.map (algebraMap (Localization.Away (l : R)) B)).comp
      (MvPolynomial.map (σ := ι) (algebraMap R (Localization.Away (l : R)))) = MvPolynomial.map (algebraMap R B) := by
    ext x
    · simp [← IsScalarTower.algebraMap_apply]
    · simp
  simp only [mapP, Polynomial.map_map, hc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNormPt
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.normPt_of :
    SameNormRing → BaseOfChart → SecChart → EtAwayChart → GenChart → PtChart → NormOfPt := by
  intro hSN hBOC hSec hEA hGen hPtC l f n hl O _ _ _ ϖ hϖ hl0 hlu Y g hg T hPt U V hU hV h
  intro B _ _ hlB I _ z hs B' _ ρ hρπ ι _ x
  set q := l ^ f with hq
  set πU := Y.presheaf.map (homOfLE le_top).op (fn g ϖ) with hπU
  letI : ∀ j, Algebra Γ(Y, U) Γ((T j).Z, (T j).p ⁻¹ᵁ U) := fun j => (T j).alg U
  obtain ⟨hBase, m, hm⟩ := hBOC l O ϖ hϖ hl0 hlu Y g hg U hU
  let s : (j : Fin (n + 1)) → ι → Γ((T j).Z, (T j).p ⁻¹ᵁ U) := fun j k =>
    ((T j).r.appLE V ((T j).p ⁻¹ᵁ U) (h j)).hom (x k) ^ (q ^ (n - (j : ℕ)))
  have hρ : ∀ a ∈ Ideal.span {πU}, ρ (algebraMap Γ(Y, U) B a) = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, map_mul, hρπ, mul_zero]
  have key := hSN l Γ(Y, U) (Ideal.span {πU}) hBase (Fin (n + 1))
    (fun j => Γ((T j).Z, (T j).p ⁻¹ᵁ U)) (fun j => (T j).d) (fun j => hEA l Y (T j) U hU)
    (wEv q) (wOd q) ι s ?_ B hlB I z hs B' ρ hρ
  · simpa only [s, map_pow] using key
  intro W _ _ _ _ _ hlW hmin J _ zz hbij
  have hgen := hGen Y (fn g ϖ) U hU W (algebraMap Γ(Y, U) W) hmin
  have hlm : (l : W) ∈ IsLocalRing.maximalIdeal W := by
    have h1 : ((l : Γ(Y, U)) ^ m) ∈ Ideal.comap (algebraMap Γ(Y, U) W) (IsLocalRing.maximalIdeal W) :=
      hmin.1.2 hm
    rw [Ideal.mem_comap, map_pow, map_natCast] at h1
    exact (IsLocalRing.maximalIdeal.isMaximal W).isPrime.mem_of_pow_mem m h1
  have hlκ : ((l : IsLocalRing.ResidueField W)) = 0 := by
    rw [← map_natCast (IsLocalRing.residue W), IsLocalRing.residue_eq_zero_iff]
    exact hlm
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : CharP (IsLocalRing.ResidueField W) l := (CharP.charP_iff_prime_eq_zero hl).mpr hlκ
  let φ := iterateFrobenius (IsLocalRing.ResidueField W) l f
  have hφ : ∀ a, φ a = a ^ q := fun a => rfl
  have hφm : ∀ (k : ℕ) a, (φ ^ k) a = a ^ (q ^ k) := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      rw [pow_succ, RingHom.mul_def, RingHom.comp_apply, ih, hφ, ← pow_mul, pow_succ']
  choose hZ hE using fun j => hSec l Y (T j) U hU
  choose e he using fun j => hE j W
  have hbij' : ∀ j, Function.Bijective (fun i => e j (zz j i)) :=
    fun j => (e j).bijective.comp (hbij j)
  have alt := hPt W hlW (ptOf hU W (algebraMap Γ(Y, U) W)) hgen φ hφ J (fun j i => e j (zz j i)) hbij'
  unfold AltId at alt
  have hterm : ∀ (j : Fin (n + 1)) (i : J j),
      (twist φ Y)^[n - (j : ℕ)] (resPt W ≫ (e j (zz j i)).1 ≫ (T j).r) =
        ptOf hV (IsLocalRing.ResidueField W) ((φ ^ (n - (j : ℕ))).comp ((IsLocalRing.residue W).comp
          ((zz j i).toRingHom.comp ((T j).r.appLE V ((T j).p ⁻¹ᵁ U) (h j)).hom))) := by
    intro j i
    rw [he j (zz j i)]
    unfold resPt
    rw [(hPtC Y V hV (IsLocalRing.ResidueField W)).2.2 (T j).Z (T j).r ((T j).p ⁻¹ᵁ U) (hZ j) (h j) W
      (IsLocalRing.residue W) (zz j i).toRingHom]
    rw [(hPtC Y V hV (IsLocalRing.ResidueField W)).2.1]
  simp only [hterm] at alt
  classical
  let G : (Spec (CommRingCat.of (IsLocalRing.ResidueField W)) ⟶ Y) → ι → IsLocalRing.ResidueField W :=
    fun P k => if hP : ∃ F, ptOf hV (IsLocalRing.ResidueField W) F = P then (Classical.choose hP) (x k) else 0
  have hG : ∀ F, G (ptOf hV (IsLocalRing.ResidueField W) F) = fun k => F (x k) := by
    intro F
    funext k
    have hP : ∃ F', ptOf hV (IsLocalRing.ResidueField W) F' = ptOf hV (IsLocalRing.ResidueField W) F := ⟨F, rfl⟩
    simp only [G, dif_pos hP]
    rw [(hPtC Y V hV (IsLocalRing.ResidueField W)).1 (Classical.choose_spec hP)]
  have alt2 := congrArg (Multiset.map G) alt
  rw [pts_map, pts_map] at alt2
  simp only [hG, RingHom.comp_apply, hφm, AlgHom.coe_toRingHom] at alt2
  simp only [s, map_pow]
  exact alt2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNormRead
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem form_map' {B B' ι : Type} [CommRing B] [CommRing B'] [Fintype ι] (f : B →+* B') (c : ι → B) :
    (form c).map (MvPolynomial.map f) = form fun k => f (c k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [form, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.map_sum, map_sum, MvPolynomial.map_C, MvPolynomial.map_X]

private theorem descend {R S B B' ι I : Type} [CommRing R] [CommRing S] [CommRing B] [CommRing B']
    [Algebra R S] [Algebra R B] [Algebra R B'] [Fintype ι] [Fintype I]
    (j : B →ₐ[R] B') (hj : Function.Injective j) (N : Polynomial (MvPolynomial ι R)) (s : ι → S)
    (z : I → (S →ₐ[R] B))
    (h : mapP (algebraMap R B') N = ∏ i, form fun k => j (z i (s k))) :
    mapP (algebraMap R B) N = ∏ i, form fun k => z i (s k) := by
  have hj' : Function.Injective (j : B →+* B') := hj
  apply Polynomial.map_injective _ (MvPolynomial.map_injective _ hj')
  rw [Polynomial.map_prod]
  have e : ∀ i, (form fun k => z i (s k)).map (MvPolynomial.map (j : B →+* B'))
      = form fun k => j (z i (s k)) := fun i => form_map' _ _
  simp only [e]
  have hc : (MvPolynomial.map (σ := ι) (j : B →+* B')).comp (MvPolynomial.map (algebraMap R B))
      = MvPolynomial.map (algebraMap R B') := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro i; simp
  rw [← h, mapP, Polynomial.map_map, hc]

theorem UpperTheory.Gal.crystallineComparison.normRead_of :
    NormInt → EtOfUnit → SplitsField → ValPts → NormRead := by
  intro hInt hEt hSF hVP l d R S _ _ _ hE hcl ι _ s
  obtain ⟨N, hN⟩ := hInt l d R S hE hcl ι s
  refine ⟨N, ?_, ?_⟩
  · intro B _ _ hl I _ z hz
    have hinj : Function.Injective (algebraMap B (Localization.Away (l : B))) :=
      IsLocalization.injective _ (Submonoid.powers_le.2 hl)
    have hu : IsUnit (l : Localization.Away (l : B)) := by
      have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (l : B)) (l : B)
      simpa using this
    have h1 := hN (Localization.Away (l : B)) hu I
      (fun i => (IsScalarTower.toAlgHom R B (Localization.Away (l : B))).comp (z i)) hz
    exact descend (IsScalarTower.toAlgHom R B (Localization.Away (l : B))) hinj N s z h1
  · intro V _ _ _ _ _ hl
    have hinj : Function.Injective (algebraMap V (FractionRing V)) :=
      IsFractionRing.injective V (FractionRing V)
    have hlK : ((l : ℕ) : FractionRing V) ≠ 0 := by
      intro h0
      apply hl
      apply hinj
      simpa using h0
    have hu : IsUnit ((l : ℕ) : FractionRing V) := hlK.isUnit
    have het : Algebra.Etale (FractionRing V) (FractionRing V ⊗[R] S) := hEt l R S _ hE.et hu
    obtain ⟨hfin, hsp⟩ := hSF R S (FractionRing V) het
    haveI := hE.fin
    have hb := hVP R S V
    have hfinV : Finite (S →ₐ[R] V) := Finite.of_injective _ hb.1
    refine ⟨hfinV, fun I _ z hz => ?_⟩
    letI := Fintype.ofFinite (S →ₐ[R] FractionRing V)
    have h1 := hN (FractionRing V) hu (S →ₐ[R] FractionRing V) (fun z => z) hsp
    refine descend (IsScalarTower.toAlgHom R V (FractionRing V)) hinj N s z ?_
    rw [h1]
    symm
    exact Fintype.prod_bijective (fun i => (IsScalarTower.toAlgHom R V (FractionRing V)).comp (z i))
      (hb.comp hz) _ _ (fun i => rfl)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPtChart
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.ptChart_of :
    PtChart := by
  intro Y V hV κ _
  refine ⟨?_, ?_, ?_⟩
  · intro f g hfg
    unfold ptOf at hfg
    have h := Spec.map_injective ((cancel_mono hV.fromSpec).mp hfg)
    exact congrArg CommRingCat.Hom.hom h
  · intro φ f m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ']
      unfold twist ptOf
      rw [← Spec.map_comp_assoc]
      rfl
  · intro Z r W hW h B _ ρ z
    unfold ptOf
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec r hV hW h, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPtOrd
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.ptOrd_of :
    OrdCount → PtIdOfOrd := by
  intro hC l q n Y π T hO V _ _ _ _ hl y hy φ hφ I _ z hz
  apply hC
  obtain ⟨k, H, x, hk, x2, x3, hf, C, A, e, h1, h2, h3, h4⟩ := hO V hl y hy φ hφ
  exact ⟨k, H, x, hk, x2, x3, hf, C, A, fun j => (Equiv.ofBijective (z j) (hz j)).trans (e j),
    h1, h2, h3, fun j i => h4 j (z j i)⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPtsProd
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.ptsProd_of :
    PtsProd := by
  intro B B' _ _ ρ ι J _ _ I _ a v
  have hf : ∀ c : ι → B, Polynomial.map (MvPolynomial.map ρ) (form c) = form (fun k => ρ (c k)) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      simp [form, Polynomial.map_sub, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
  have key : ∀ (m : J → Multiset (ι → B')) (s : Finset J),
      (Multiset.map form (∑ j ∈ s, a j • m j)).prod = ∏ j ∈ s, (Multiset.map form (m j)).prod ^ a j := by
    intro m s
    classical
    refine Finset.induction_on s (by simp) ?_
    intro j s hj ih
    rw [Finset.sum_insert hj, Finset.prod_insert hj, Multiset.map_add (f := _), Multiset.prod_add, ih,
      Multiset.map_nsmul, Multiset.prod_nsmul]
  simp only [pts, mapP]
  rw [key, Polynomial.map_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [Polynomial.map_pow, Polynomial.map_prod, Multiset.map_map]
  congr 1
  rw [Finset.prod_eq_multiset_prod]
  simp [Function.comp_def, hf]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PRankDeg
section
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.rankDeg_of :
    SplitsField → RankOfDeg := by
  intro hSF A S _ _ _ _ _ d hd
  funext p
  letI : Algebra A (AlgebraicClosure p.asIdeal.ResidueField) :=
    ((algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)).comp
      (algebraMap A p.asIdeal.ResidueField)).toAlgebra
  let q : PrimeSpectrum (AlgebraicClosure p.asIdeal.ResidueField) := ⟨⊥, Ideal.isPrime_bot⟩
  have hq : PrimeSpectrum.comap (algebraMap A (AlgebraicClosure p.asIdeal.ResidueField)) q = p := by
    ext x
    change algebraMap A (AlgebraicClosure p.asIdeal.ResidueField) x ∈ (⊥ : Ideal _) ↔ x ∈ p.asIdeal
    rw [Ideal.mem_bot]
    change algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)
      (algebraMap A p.asIdeal.ResidueField x) = 0 ↔ x ∈ p.asIdeal
    rw [map_eq_zero_iff _ (algebraMap p.asIdeal.ResidueField _).injective,
      Ideal.algebraMap_residueField_eq_zero]
  rw [← hq, ← Module.rankAtStalk_baseChange q, Module.rankAtStalk_eq_finrank_of_free]
  obtain ⟨hfin, hsp⟩ := hSF A S (AlgebraicClosure p.asIdeal.ResidueField) inferInstance
  haveI := Fintype.ofFinite (S →ₐ[A] AlgebraicClosure p.asIdeal.ResidueField)
  have e := AlgEquiv.ofBijective (splitMap fun z => z) hsp
  have h1 := e.toLinearEquiv.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card,
    hd (AlgebraicClosure p.asIdeal.ResidueField)] at h1
  simp [h1]
end

