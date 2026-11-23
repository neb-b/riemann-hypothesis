module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.StCoiLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrDet
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem gdet_eq_ofRep {n : ℕ} {A G E S : Type} [CommRing A] [Group G] [Ring E] [Algebra A E] [CommRing S]
    [Algebra A S] (D : GDet n A G) (DE : Det n A E) (ι : MonoidAlgebra A G →ₐ[A] E) (hp : DE.pull ι = D.toDet)
    (hch : DE.IsCH) (ep : Fin n → E) (he : CompleteOrthogonalIdempotents ep)
    (h1 : ∀ i, DE.D A[X] (1 + X ⊗ₜ ep i) = 1 + X) (φ : E →ₐ[A] Matrix (Fin n) (Fin n) S)
    (hφ : ∀ i, φ (ep i) = single i i 1) (vr : G →* Matrix (Fin n) (Fin n) S)
    (hvr : ∀ γ, vr γ = φ (ι (MonoidAlgebra.single γ 1))) :
    D.map (algebraMap A S) = GDet.ofRep vr := by
  refine GDet.ext fun T _ _ y => ?_
  letI : Algebra A T := ((algebraMap S T).comp (algebraMap A S)).toAlgebra
  haveI : IsScalarTower A S T := .of_algebraMap_eq fun _ => rfl
  let ψ : T ⊗[A] E →ₐ[T] Matrix (Fin n) (Fin n) T :=
    Algebra.TensorProduct.lift (Algebra.ofId T _) ((IsScalarTower.toAlgHom A S T).mapMatrix.comp φ)
      fun s _ => Algebra.commute_algebraMap_left s _
  have hψ : ∀ (t : T) (z : E), ψ (t ⊗ₜ z) = t • (φ z).map (algebraMap S T) := fun t z =>
    (Algebra.TensorProduct.lift_tmul _ _ _ t z).trans (Algebra.smul_def _ _).symm
  have hD : ∀ w : T ⊗[A] E, DE.D T w = (ψ w).det := by
    intro w
    obtain ⟨k, t, z, rfl⟩ := TensorProduct.exists_sum_tmul_eq w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [d_gma_det DE ep hch he h1 S φ hφ T t z, map_sum]
    simp only [hψ]
  have h2 : D.D T y = DE.D T (Algebra.TensorProduct.map (AlgHom.id T T) ι (toT A G T y)) := by
    have h3 : D.D T y = D.toDet.D T (toT A G T y) := (congrArg (D.D T) (ofT_toT (A := A) y)).symm
    rw [h3, ← hp]
    rfl
  change D.D T y = (GDet.repAlg vr T y).det
  rw [h2, hD]
  clear h2
  congr 1
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g s =>
    rw [toT_single, Algebra.TensorProduct.map_tmul, hψ, ← hvr]
    simp [GDet.repAlg]

theorem UpperTheory.V.Pa.gr_det :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {B : Type} [CommRing B] [IsLocalRing B] {D : GDet n B G.G₀} {I : Set (MonoidAlgebra B G.G₀)} {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)] {e : G.G₀ →* Bˣ} (H : Hat h x D I Bh e) {ep : Fin n → H.E} (g : GrAlg H.T n x.a H.r ep), CompleteOrthogonalIdempotents ep → (∀ i, H.DE.D Bh[X] (1 + X ⊗ₜ ep i) = 1 + X) → ∀ vr : G.G₀ →* Matrix (Fin n) (Fin n) g.AA, (∀ γ, vr γ = g.φ (H.ι (MonoidAlgebra.single γ 1))) → D.map ((algebraMap Bh g.AA).comp (algebraMap B Bh)) = GDet.ofRep vr := by
  intro l _ L G G0 h n x B _ _ D I Bh _ _ _ _ e H ep g he h1 vr hvr
  rw [← (d_gmap D).2.1]
  exact gdet_eq_ofRep _ H.DE H.ι H.pull H.ch ep he h1 g.φ g.φ_ep vr hvr
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrThick
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem quot_ss {B Bh E κ Γ : Type} [CommRing B] [CommRing Bh] [Algebra B Bh] [Ring E] [Algebra Bh E]
    [Field κ] [Algebra Bh κ] [Group Γ] (I : Set (MonoidAlgebra B Γ))
    (ι : MonoidAlgebra Bh Γ →ₐ[Bh] E) (surj : Function.Surjective ι)
    (ker : ∀ y, ι y = 0 → y ∈ TwoSidedIdeal.span (MonoidAlgebra.mapRingHom Γ (algebraMap B Bh) '' I))
    [IsSemisimpleRing (κ ⊗[Bh] E)] :
    IsSemisimpleRing (TwoSidedIdeal.span
      (MonoidAlgebra.mapRingHom Γ ((algebraMap Bh κ).comp (algebraMap B Bh)) '' I)).ringCon.Quotient := by
  set J := TwoSidedIdeal.span
      (MonoidAlgebra.mapRingHom Γ ((algebraMap Bh κ).comp (algebraMap B Bh)) '' I) with hJ
  let π : MonoidAlgebra κ Γ →+* J.ringCon.Quotient := J.ringCon.mk'
  have hπ : ∀ z, z ∈ J → π z = 0 := by
    intro z hz
    rw [← map_zero π]
    exact (RingCon.eq _).2 ((TwoSidedIdeal.mem_iff _ _).1 hz)
  let ψ0 : MonoidAlgebra Bh Γ →+* J.ringCon.Quotient :=
    π.comp (MonoidAlgebra.mapRingHom Γ (algebraMap Bh κ))
  have hk : RingHom.ker ι.toRingHom ≤ RingHom.ker ψ0 := by
    intro y hy
    have h1 := ker y hy
    have h2 : TwoSidedIdeal.span (MonoidAlgebra.mapRingHom Γ (algebraMap B Bh) '' I) ≤ TwoSidedIdeal.ker ψ0 := by
      rw [TwoSidedIdeal.span_le]
      rintro _ ⟨z, hz, rfl⟩
      rw [SetLike.mem_coe, TwoSidedIdeal.mem_ker]
      apply hπ
      apply TwoSidedIdeal.subset_span
      refine ⟨z, hz, ?_⟩
      ext a
      simp
    exact (TwoSidedIdeal.mem_ker _).1 (h2 h1)
  let ψ : E →+* J.ringCon.Quotient := ι.toRingHom.liftOfSurjective surj ⟨ψ0, hk⟩
  have hψ : ∀ y, ψ (ι y) = ψ0 y := fun y => RingHom.liftOfSurjective_comp_apply ι.toRingHom surj ⟨ψ0, hk⟩ y
  let ψa : E →ₐ[Bh] J.ringCon.Quotient :=
    { ψ with
      commutes' := fun b => by
        change ψ (algebraMap Bh E b) = π (algebraMap Bh (MonoidAlgebra κ Γ) b)
        rw [← ι.commutes, hψ]
        change π _ = _
        congr 1
        simp [MonoidAlgebra.coe_algebraMap] }
  let ka : κ →ₐ[Bh] J.ringCon.Quotient :=
    { π.comp (algebraMap κ (MonoidAlgebra κ Γ)) with
      commutes' := fun b => by
        change π _ = π (algebraMap Bh (MonoidAlgebra κ Γ) b)
        congr 1 }
  have hc : ∀ a y, Commute (ka a) (ψa y) := by
    intro a y
    obtain ⟨y, rfl⟩ := surj y
    change Commute (π (algebraMap κ _ a)) (ψ (ι y))
    rw [hψ]
    exact Commute.map (Algebra.commutes a _) π
  let Φ := Algebra.TensorProduct.lift ka ψa hc
  refine RingHom.isSemisimpleRing_of_surjective Φ.toRingHom ?_
  intro w
  obtain ⟨w, rfl⟩ : ∃ z, π z = w := J.ringCon.mk'_surjective w
  induction w using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add u v hu hv =>
    obtain ⟨a, ha⟩ := hu
    obtain ⟨b, hb⟩ := hv
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩
  | single m a =>
    refine ⟨a ⊗ₜ ι (MonoidAlgebra.single m 1), ?_⟩
    change Φ _ = _
    rw [Algebra.TensorProduct.lift_tmul]
    change π (algebraMap κ _ a) * ψ (ι _) = _
    rw [hψ]
    change π _ * π _ = _
    rw [← map_mul]
    congr 1
    simp [MonoidAlgebra.coe_algebraMap, MonoidAlgebra.single_mul_single]

theorem UpperTheory.V.Pa.gr_thick :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {B : Type} [CommRing B] [IsLocalRing B] {D : GDet n B G.G₀} {I : Set (MonoidAlgebra B G.G₀)} {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)] {e : G.G₀ →* Bˣ} (H : Hat h x D I Bh e) {ep : Fin n → H.E} (g : GrAlg H.T n x.a H.r ep), ∀ Q : Ideal Bh, Q.IsPrime → NonSS I (algebraMap B Bh) Q → Module.annihilator Bh g.N ≤ Q := by
  intro l _ L G G0 h n x B _ _ D I Bh _ _ _ _ e H ep g Q _ hQ s hs
  obtain ⟨κ, _, f, hf, hns⟩ := hQ
  by_contra hsQ
  letI : Algebra Bh κ := f.toAlgebra
  have hs0 : algebraMap Bh κ s ≠ 0 := fun h0 => hsQ (hf ▸ (RingHom.mem_ker.2 h0 : s ∈ RingHom.ker f))
  haveI := UpperTheory.V.Pa.gr_ss g κ s hs0 hs
  exact hns (quot_ss (κ := κ) I H.ι H.surj (fun y hy => (H.ker y).1 hy))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.HatSt
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.hat_st :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)], (∀ b, algebraMap Bh (FractionRing x.A) (algebraMap B Bh b) = algebraMap x.A (FractionRing x.A) (P.f b)) → ∀ H : Hat h x u.D P.ker Bh (G.frame.eps O B), ∀ y, H.r (H.T.st y) = (H.r y)ᵀ := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ _ hf H
  have key : ∀ g : G.G₀, (algebraMap B Bh) ↑((G.frame.eps O B) g ^ (1 - (n : ℤ))) •
      ((mat x.ρ) (h.p₀ (G.frame.conj g)⁻¹)).map (algebraMap x.A (FractionRing x.A)) =
      (((mat x.ρ) (h.p₀ g)).map (algebraMap x.A (FractionRing x.A)))ᵀ := by
    intro g
    obtain ⟨he, hc⟩ := eps_eq P g
    have hunit : P.f (↑((G.frame.eps O B) g ^ (1 - (n : ℤ))) : B) =
        ↑((G0.frame.eps ℤ_[l] x.A) (h.p₀ g) ^ (1 - (n : ℤ))) := by
      have hu : Units.map (P.f : B →* x.A) ((G.frame.eps O B) g) =
          (G0.frame.eps ℤ_[l] x.A) (h.p₀ g) := by
        apply Units.ext
        rw [Units.coe_map]
        exact he
      rw [← hu, ← map_zpow (Units.map (P.f : B →* x.A)), Units.coe_map]
      rfl
    have hinvM : (mat x.ρ) (h.p₀ (G.frame.conj g)) * (mat x.ρ) (h.p₀ (G.frame.conj g)⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
    have hA : ((mat x.ρ) (h.p₀ g))ᵀ =
        (↑((G0.frame.eps ℤ_[l] x.A) (h.p₀ g) ^ (1 - (n : ℤ))) : x.A) •
          (mat x.ρ) (h.p₀ (G.frame.conj g)⁻¹) := by
      have hform := x.form (h.p₀ g)
      rw [Units.val_one, Matrix.mul_one, ← hc] at hform
      calc ((mat x.ρ) (h.p₀ g))ᵀ = ((mat x.ρ) (h.p₀ g))ᵀ * ((mat x.ρ) (h.p₀ (G.frame.conj g)) *
            (mat x.ρ) (h.p₀ (G.frame.conj g)⁻¹)) := by rw [hinvM, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, hform, Matrix.smul_mul, Matrix.one_mul]
    rw [← Matrix.transpose_map, hA]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul]
    rw [Algebra.smul_def, hf, hunit]
  intro y
  obtain ⟨z, rfl⟩ := H.surj y
  refine MonoidAlgebra.induction_on (motive := fun z => H.r (H.T.st (H.ι z)) = (H.r (H.ι z))ᵀ)
    z ?_ ?_ ?_
  · intro g
    rw [MonoidAlgebra.of_apply, H.st, map_smul, H.r_ι, H.r_ι]
    exact key g
  · intro a b ha hb
    simp only [map_add (f := _), ha, hb, Matrix.transpose_add]
  · intro c a ha
    simp only [map_smul, ha, Matrix.transpose_smul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.OBLt
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem oB_lt {n a : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ n) (i : Fin n) :
    ((oB n a i : Fin n) : ℕ) < a ↔ (i : ℕ) < a := by
  unfold oB
  split_ifs with hi
  · simp only [hi, iff_true]
    exact h1
  · simp only [hi, iff_false, not_lt]
    have := i.2
    omega

private theorem oB_oB {n a : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ n) (i : Fin n) : oB n a (oB n a i) = oB n a i := by
  have key := oB_lt h1 h2 i
  unfold oB at key ⊢
  by_cases hi : (i : ℕ) < a
  · have : ((if (i : ℕ) < a then (⟨0, by omega⟩ : Fin n) else ⟨n - 1, by omega⟩ : Fin n) : ℕ) < a := key.2 hi
    simp only [hi, if_true] at this ⊢
    simp only [this, if_true]
  · have : ¬ ((if (i : ℕ) < a then (⟨0, by omega⟩ : Fin n) else ⟨n - 1, by omega⟩ : Fin n) : ℕ) < a :=
      fun h => hi (key.1 h)
    simp only [hi, if_false] at this ⊢
    simp only [this, if_false]

private theorem single_mem {F : Type} [Field F] {n a : ℕ} (p q : Fin n) (h : (p : ℕ) < a ↔ (q : ℕ) < a) :
    (single p q 1 : Matrix (Fin n) (Fin n) F) ∈ Ev F F n a := by
  intro i j
  refine ⟨fun _ => Submodule.mem_top, fun hij => ?_⟩
  rw [Matrix.single_apply]
  split_ifs with hpq
  · obtain ⟨rfl, rfl⟩ := hpq
    exact absurd h hij
  · exact Submodule.zero_mem _

theorem UpperTheory.V.Pa.idem :
    ∀ {B E F : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field F] [Algebra B F] {n : ℕ} [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [Module.Finite B E] (a : ℕ) (D : Det n B E) (T : TrInv B E) (r : E →ₐ[B] Matrix (Fin n) (Fin n) F), 1 ≤ a → a ≤ n → IsUnit (2 : B) → D.IsCH → (∀ y, T.tr y = D.tr y) → RingHom.ker (algebraMap B F) = maximalIdeal B → (∀ y, (D.chi y).map (algebraMap B F) = (r y).charpoly) → (∀ y, r (T.st y) = (r y)ᵀ) → (∀ Z ∈ Ev F F n a, ∃ y, r y = Z) → ∃ U : T.Units (Fin n) (oB n a), (∀ i, r (U.x i) = single (oB n a i) i 1) ∧ ∀ i, D.D B[X] (1 + X ⊗ₜ U.ep i) = 1 + X := by
  intro B E F _ _ _ _ _ _ n _ _ _ a D T r h1 h2 h2u hCH htr hker hchi hst hsurj
  have hn : 1 ≤ n := le_trans h1 h2
  haveI : IsAdicComplete (maximalIdeal B) E := GlobalTheory.isAdicComplete_of_finite (maximalIdeal B) E
  obtain ⟨hnil, hidem⟩ := idem_nil D r hCH hker hchi
  have hdiag : ∀ i : Fin n, ∃ y, r y = single i i 1 := fun i =>
    hsurj _ (single_mem i i Iff.rfl)
  obtain ⟨ep, hcoi, hstep, hrep⟩ :=
    st_coi_lift T (maximalIdeal B) r h2u (le_of_eq hker.symm) hnil hst hdiag
  have hD : ∀ i, D.D B[X] (1 + X ⊗ₜ ep i) = 1 + X := fun i =>
    hidem (ep i) i (hcoi.idem i) (hrep i)
  have hcorner := fun i => d_corner D (ep i) hCH (hcoi.idem i) (hD i) hn
  haveI : HenselianRing B (RingHom.ker (algebraMap B F)) := by
    rw [hker]
    infer_instance
  obtain ⟨U, hUep, hUx⟩ := units_exist T (oB n a) r ep h2u (fun i => oB_oB h1 h2 i) hst
    (fun i => hsurj _ (single_mem _ _ (oB_lt h1 h2 i))) hcoi hstep hrep
    (fun i => by rw [htr]; exact (hcorner i).2.1)
    (fun i y => ⟨D.tr (ep i * y), (hcorner i).1 y⟩)
  refine ⟨U, hUx, fun i => ?_⟩
  rw [hUep]
  exact hD i
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.RFSurj
section
noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Pa

theorem rF_surj : ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K]
    {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u)
    {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)],
    (∀ b, algebraMap Bh (FractionRing x.A) (algebraMap B Bh b) = algebraMap x.A (FractionRing x.A) (P.f b)) →
    RingHom.ker (algebraMap Bh (FractionRing x.A)) = maximalIdeal Bh →
    Function.Surjective (algebraMap Bh (FractionRing x.A)) := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ _ hcomp hker z
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors x.A) z
  obtain ⟨a', rfl⟩ := (f_surj P).1 a
  obtain ⟨b', hb'⟩ := (f_surj P).1 (b : x.A)
  have hu : IsUnit (algebraMap B Bh b') := by
    by_contra hn
    have hm : algebraMap B Bh b' ∈ maximalIdeal Bh := (mem_maximalIdeal _).2 hn
    rw [← hker, RingHom.mem_ker, hcomp, hb'] at hm
    exact nonZeroDivisors.coe_ne_zero b
      ((IsFractionRing.injective x.A (FractionRing x.A)) (hm.trans (map_zero _).symm))
  obtain ⟨v, hv⟩ := hu
  refine ⟨algebraMap B Bh a' * ↑v⁻¹, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, ← hb', ← hcomp, ← hv, ← map_mul, mul_assoc,
    Units.inv_mul, mul_one, hcomp]

end UpperTheory.V.Pa
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.RepStar
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.rep_star :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ y, P.rep (G.frame.star O B n y) = (P.rep y)ᵀ := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P y
  have sb := star_basic G.frame n O B
  have hrep : ∀ (g : G.G₀) (b : B), P.rep (MonoidAlgebra.single g b) = P.f b • mat x.ρ (h.p₀ g) := by
    intro g b
    simp only [OoPt.rep, GDet.repAlg, RingHom.comp_apply, MonoidAlgebra.mapRingHom_single,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.comp_apply,
      Algebra.algebraMap_self, RingHom.mapMatrix_id]
    rfl
  induction y using MonoidAlgebra.induction_linear with
  | zero =>
    have h0 : G.frame.star O B n 0 = 0 := by simpa using sb.2.2.2.2.2.1 0 0
    rw [h0, map_zero, Matrix.transpose_zero]
  | add p q hp hq => rw [sb.2.2.1, map_add (f := _), map_add (f := _), hp, hq, Matrix.transpose_add]
  | single g b =>
    rw [sb.2.2.2.2.2.2 g b]
    obtain ⟨he, hc⟩ := eps_eq P g
    have hform := x.form (h.p₀ g)
    rw [Units.val_one, mul_one] at hform
    have hci : mat x.ρ (G0.frame.conj (h.p₀ g)) * mat x.ρ (G0.frame.conj (h.p₀ g))⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have hT : (mat x.ρ (h.p₀ g))ᵀ =
        ((G0.frame.eps ℤ_[l] (PowerSeries x.K) (h.p₀ g) ^ (1 - (n : ℤ)) : (PowerSeries x.K)ˣ) : PowerSeries x.K) •
          mat x.ρ (G0.frame.conj (h.p₀ g))⁻¹ := by
      calc (mat x.ρ (h.p₀ g))ᵀ
          = (mat x.ρ (h.p₀ g))ᵀ * (mat x.ρ (G0.frame.conj (h.p₀ g)) * mat x.ρ (G0.frame.conj (h.p₀ g))⁻¹) := by
            rw [hci, mul_one]
        _ = _ := by rw [← mul_assoc, hform, Matrix.smul_mul, one_mul]
    have hu : Units.map (P.f.toRingHom : B →* x.A) (G.frame.eps O B g) = G0.frame.eps ℤ_[l] x.A (h.p₀ g) :=
      Units.ext he
    have hfu : P.f ((G.frame.eps O B g ^ (1 - (n : ℤ)) : Bˣ) : B) =
        ((G0.frame.eps ℤ_[l] x.A (h.p₀ g) ^ (1 - (n : ℤ)) : (x.A)ˣ) : x.A) := by
      calc P.f ((G.frame.eps O B g ^ (1 - (n : ℤ)) : Bˣ) : B)
          = ((Units.map (P.f.toRingHom : B →* x.A) (G.frame.eps O B g ^ (1 - (n : ℤ))) : (x.A)ˣ) : x.A) := rfl
        _ = _ := by rw [map_zpow, hu]
    rw [hrep, hrep, Matrix.transpose_smul, map_mul, hfu, hT, map_inv, hc, mul_smul]
end

