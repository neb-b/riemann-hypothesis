module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.AdmCrys
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0808

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.MatInS
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC TensorProduct
open Formalism.BasicNotions.Loc Formalism.MainNotions.N CrystallineSemistableComparison UpperTheory.Gal.Int.Geo
open GlobalTheory.GalV (HTower Htot hop galV galTot pullTot)
open UpperTheory.Gal.Seam

open TensorProduct in
private theorem core {Q L : Type*} [Field Q] [Field L] [Algebra Q L] {V : ℤ → Type*} [∀ n, AddCommGroup (V n)] [∀ n, Module Q (V n)]
    (hneg : ∀ n : ℤ, n < 0 → Subsingleton (V n)) (hfin : ∀ n, FiniteDimensional Q (V n))
    {U G : Type*} [AddCommGroup U] [Module L U] (g : G → ∀ n, V n →ₗ[Q] V n)
    (φ : (L ⊗[Q] DirectSum ℤ V) →ₗ[L] U) (hφ : Function.Injective φ) (gU : G → U →ₗ[L] U)
    (hc : ∀ σ, gU σ ∘ₗ φ = φ ∘ₗ (DirectSum.lmap (g σ)).baseChange L)
    {d : ℕ} (v : Fin d → U) (hv : LinearIndependent L v) (hr : ∀ j, v j ∈ LinearMap.range φ)
    (ρ : G → Matrix (Fin d) (Fin d) L) (hρ : ∀ σ j, gU σ (v j) = ∑ i, ρ σ i j • v i) :
    ∃ (N : ℕ) (a : Fin N → ℕ) (b : ∀ n : Fin N, Module.Basis (Fin (a n)) Q (V ((n : ℕ) : ℤ)))
      (M : Matrix (Σ n, Fin (a n)) (Fin d) L), Function.Injective M.mulVec ∧ ∀ σ,
        (Matrix.blockDiagonal' fun n : Fin N => LinearMap.toMatrix (b n) (b n) (g σ ((n : ℕ) : ℤ))).map (algebraMap Q L) * M =
          M * ρ σ := by
  classical
  choose y hy using hr
  let e := TensorProduct.directSumRight Q L L V
  let π : ∀ n : ℤ, (L ⊗[Q] DirectSum ℤ V) →ₗ[L] L ⊗[Q] V n := fun n =>
    (DirectSum.component L ℤ (fun i => L ⊗[Q] V i) n) ∘ₗ e.toLinearMap
  have hπ0 : ∀ w, (∀ n, π n w = 0) → w = 0 := fun w h => by
    apply e.injective
    rw [map_zero]
    exact DFinsupp.ext fun n => h n
  have hπt : ∀ (n : ℤ) (t : L) (x : DirectSum ℤ V), π n (t ⊗ₜ[Q] x) = t ⊗ₜ[Q] (x n) := fun n t x => by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i z =>
      have h1 : π n (t ⊗ₜ[Q] (DirectSum.of V i z)) =
          DirectSum.component L ℤ (fun i => L ⊗[Q] V i) n (DirectSum.lof L ℤ (fun i => L ⊗[Q] V i) i (t ⊗ₜ[Q] z)) := by
        change DirectSum.component L ℤ (fun i => L ⊗[Q] V i) n (e (t ⊗ₜ[Q] (DirectSum.lof Q ℤ V i z))) = _
        rw [TensorProduct.directSumRight_tmul_lof]
      rw [h1]
      by_cases hi : i = n
      · subst hi
        rw [DirectSum.component.lof_self]
        simp
      · change (DirectSum.lof L ℤ (fun i => L ⊗[Q] V i) i (t ⊗ₜ[Q] z)) n = _
        rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hi), DirectSum.of_eq_of_ne _ _ _ (Ne.symm hi),
          TensorProduct.tmul_zero]
    | add x₁ x₂ h₁ h₂ =>
      rw [TensorProduct.tmul_add, map_add (f := _), h₁, h₂, DirectSum.add_apply, TensorProduct.tmul_add]
  have hnat : ∀ σ n w, π n ((DirectSum.lmap (g σ)).baseChange L w) = (g σ n).baseChange L (π n w) := fun σ n w => by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul t x =>
      rw [LinearMap.baseChange_tmul, hπt, hπt, LinearMap.baseChange_tmul, DirectSum.lmap_apply]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hsupp : ∀ w, ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) ≤ n → π n w = 0 := fun w => by
    refine ⟨(DFinsupp.support (e w)).sup Int.toNat + 1, fun n hn => ?_⟩
    by_contra h
    have hm : n ∈ DFinsupp.support (e w) := DFinsupp.mem_support_iff.2 h
    have := Finset.le_sup (f := Int.toNat) hm
    push_cast at hn
    omega
  have hnegπ : ∀ (n : ℤ) w, n < 0 → π n w = 0 := fun n w hn => by
    haveI := hneg n hn
    generalize π n w = u
    induction u using TensorProduct.induction_on with
    | zero => rfl
    | tmul t x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  choose Nf hNf using fun j => hsupp (y j)
  let N := Finset.univ.sup Nf
  have hbig : ∀ j (n : ℤ), (N : ℤ) ≤ n → π n (y j) = 0 := fun j n hn =>
    hNf j n (le_trans (by exact_mod_cast Finset.le_sup (f := Nf) (Finset.mem_univ j)) hn)
  let a : Fin N → ℕ := fun n => Module.finrank Q (V ((n : ℕ) : ℤ))
  let b : ∀ n : Fin N, Module.Basis (Fin (a n)) Q (V ((n : ℕ) : ℤ)) := fun n => Module.finBasis Q _
  let B : ∀ n : Fin N, Module.Basis (Fin (a n)) L (L ⊗[Q] V ((n : ℕ) : ℤ)) := fun n => Algebra.TensorProduct.basis L (b n)
  let M : Matrix (Σ n, Fin (a n)) (Fin d) L := fun p j => (B p.1).repr (π _ (y j)) p.2
  have hG : ∀ σ j, (DirectSum.lmap (g σ)).baseChange L (y j) = ∑ i, ρ σ i j • y i := fun σ j => by
    apply hφ
    have h := LinearMap.congr_fun (hc σ) (y j)
    simp only [LinearMap.comp_apply] at h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h, hy, hρ, map_sum]
    simp only [map_smul, hy]
  have key : ∀ c : Fin d → L, M.mulVec c = 0 → c = 0 := fun c hcz => by
    have hw : (∑ j, c j • y j) = 0 := by
      apply hπ0
      intro m
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul]
      rcases lt_or_ge m 0 with hm | hm
      · simp [hnegπ m _ hm]
      rcases lt_or_ge m (N : ℤ) with hN | hN
      · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
        have hk : k < N := by exact_mod_cast hN
        let n : Fin N := ⟨k, hk⟩
        apply (B n).repr.injective
        ext i
        have := congrFun hcz ⟨n, i⟩
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, map_zero, Finset.sum_apply', Finsupp.smul_apply, Finsupp.coe_smul,
          Pi.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply]
        rw [← this]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      · simp [hbig _ m hN]
    have h0 : ∑ j, c j • v j = 0 := by
      have := congrArg φ hw
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, hy] using this
    funext j
    exact Fintype.linearIndependent_iff.1 hv c h0 j
  refine ⟨N, a, b, M, fun c c' h => ?_, fun σ => ?_⟩
  · have := key (c - c') (by rw [Matrix.mulVec_sub, h, sub_self])
    exact sub_eq_zero.1 this
  · ext ⟨n, i⟩ j
    have h1 : (B n).repr ((g σ ((n : ℕ) : ℤ)).baseChange L (π _ (y j))) i =
        ∑ k, algebraMap Q L (LinearMap.toMatrix (b n) (b n) (g σ ((n : ℕ) : ℤ)) i k) * (B n).repr (π _ (y j)) k := by
      rw [← LinearMap.toMatrix_mulVec_repr (B n) (B n)]
      simp only [B, LinearMap.toMatrix_baseChange]
      rfl
    have h2 : (g σ ((n : ℕ) : ℤ)).baseChange L (π _ (y j)) = ∑ i', ρ σ i' j • π _ (y i') := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hnat, hG, map_sum]
      simp only [map_smul]
    rw [h2] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finset.sum_apply', Finsupp.smul_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul] at h1
    rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single n]
    · simp only [Matrix.map_apply, Matrix.blockDiagonal'_apply_eq]
      rw [← h1]
      exact Finset.sum_congr rfl fun x _ => mul_comm _ _
    · intro m _ hm
      refine Finset.sum_eq_zero fun k _ => ?_
      simp [Matrix.blockDiagonal'_apply_ne _ _ _ hm.symm]
    · simp

theorem UpperTheory.Gal.Seam.matInS :
    GlobalTheory.GalV.VFin → PieceIn → NegVan → MatIn := by
  intro hV hP hN l _ K H θ hH C hC d ρ₁ hM
  obtain ⟨hinj, hle, heq⟩ := hP l K.1 (Om l) H θ hH C hC
  obtain ⟨b, hb⟩ := hM
  haveI hpr : IsProper C.p := by
    obtain ⟨n, i, hi, e⟩ := C.proj
    haveI := hi
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str ↥(OK l K.1) n
    rw [← e]
    infer_instance
  haveI hq : IsProper (mod C).q := by
    change IsProper (pullback.snd C.p _)
    infer_instance
  haveI hg : IsProper (pullback.snd (mod C).q (Spec.map (CommRingCat.ofHom (algebraMap ↥K.1 (PadicAlgCl l))))) := inferInstance
  have hunit : IsUnit ((l : ℕ) : PadicAlgCl l) :=
    (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero).isUnit
  have hfin := fun n : ℤ => (hV l (PadicAlgCl l) hunit
    (pullback.snd (mod C).q (Spec.map (CommRingCat.ofHom (algebraMap ↥K.1 (PadicAlgCl l))))) n 0).2
  obtain ⟨N, a, c, M, hMi, hMe⟩ := core (Q := ℚ_[l]) (L := Om l)
    (V := fun n : ℤ => HQ l (sch.obj (GlobalTheory.Et.geom (PadicAlgCl l) (mod C).q)) n 0) (G := ↥(GK K))
    (fun n hn => hN l _ n hn) hfin
    (fun σ n => galHQ l (PadicAlgCl l) (mod C).q n 0 (IntermediateField.fixingSubgroupEquiv K.1 σ))
    ((pullTot l (sch.map (toMod C))).baseChange (Om l)) hinj
    (fun σ => galV l H (PadicAlgCl l) (Om l) (IntermediateField.fixingSubgroupEquiv K.1 σ))
    (fun σ => by
      have h := heq (IntermediateField.fixingSubgroupEquiv K.1 σ)
      have h2 := congrArg (LinearMap.baseChange (Om l)) h
      rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at h2
      exact h2)
    (fun j => (b j).1)
    (b.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _))
    (fun j => hle (b j).2)
    (fun σ => (ρ₁ (IntermediateField.fixingSubgroupEquiv K.1 σ) : Matrix (Fin d) (Fin d) (Om l)))
    (fun σ j => hb _ j)
  exact ⟨N, a, c, M, hMi, fun σ => hMe σ⟩
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.PieceInS
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV TensorProduct
open UpperTheory.Gal.Seam

private theorem tot_inj (hV : VInv) (l : ℕ) [Fact l.Prime] {W Z : Scheme.{0}} (c : W ⟶ Z) (G : Type) [Group G] [Finite G]
    (a : G → (W ⟶ W)) (h : IsGalois c G a) : Function.Injective (pullTot l (sch.map c)) := by
  obtain ⟨h1, h2, h3, -, -, hs, hi⟩ := h
  letI : Fintype G := Fintype.ofFinite G
  exact (DirectSum.lmap_injective _).2 fun n => (hV l c G a hs hi n 0).1

private theorem tot_range (hV : VInv) (l : ℕ) [Fact l.Prime] {W Z : Scheme.{0}} (c : W ⟶ Z) (G : Type) [Group G] [Finite G]
    (a : G → (W ⟶ W)) (h : IsGalois c G a) (x : Htot l (sch.obj W))
    (hx : ∀ g, pullTot l (sch.map (a g)) x = x) : x ∈ LinearMap.range (pullTot l (sch.map c)) := by
  classical
  obtain ⟨h1, h2, h3, -, -, hs, hi⟩ := h
  letI : Fintype G := Fintype.ofFinite G
  have key : ∀ n : ℤ, x n ∈ LinearMap.range (pullHQ l (sch.map c) n 0) := fun n => by
    rw [(hV l c G a hs hi n 0).2]
    refine (Submodule.mem_iInf _).2 fun g => ?_
    have e := congrArg (fun u : Htot l (sch.obj W) => u n) (hx g)
    simp only [pullTot, DirectSum.lmap_apply] at e
    simp [LinearMap.mem_ker, sub_eq_zero, e]
  rw [← DirectSum.sum_support_of x]
  refine Submodule.sum_mem _ fun n _ => ?_
  obtain ⟨z, hz⟩ := key n
  refine ⟨DirectSum.lof ℚ_[l] ℤ (fun n => HQ l (sch.obj Z) n 0) n z, ?_⟩
  rw [pullTot, DirectSum.lmap_lof, hz]
  rfl

private theorem corr_iso (hV : VInv) (l : ℕ) [Fact l.Prime] {Z Y : Scheme.{0}} [Nonempty Z] (s : Y ⟶ Z) [IsIso s] (b : Z ⟶ Z)
    (A : Htot l (sch.obj Z) →ₗ[ℚ_[l]] Htot l (sch.obj Z)) (h : IsCorrOp l s (s ≫ b) A) :
    A = pullTot l (sch.map b) := by
  obtain ⟨W, c, G, _, _, a, J, _, σ, hG, hS, hx⟩ := h
  have hinj := tot_inj hV l c G a hG
  have hsur : Surjective c := hG.2.2.1
  obtain ⟨hσ, -⟩ := id hS
  obtain ⟨z⟩ := ‹Nonempty Z›
  obtain ⟨w, -⟩ := hsur.surj z
  let pt : UpperTheory.Gal.G3.sp (W.residueField w) ⟶ W := W.fromSpecResidueField w
  obtain ⟨j₀, -, hj⟩ := UpperTheory.Gal.G3.pPtsOfSplits s c J σ hS (W.residueField w) pt (pt ≫ c ≫ inv s) (by simp)
  have hall : ∀ j, j = j₀ := fun j => hj j (by
    have : σ j = c ≫ inv s := by rw [← hσ j]; simp
    change pt ≫ σ j = pt ≫ c ≫ inv s
    rw [this])
  haveI : Unique J := ⟨⟨j₀⟩, hall⟩
  refine LinearMap.ext fun x => hinj ?_
  rw [hx x, Fintype.sum_unique]
  have e : σ default ≫ s ≫ b = c ≫ b := by rw [← Category.assoc, hσ]
  rw [e, Functor.map_comp, pullTot_comp]
  rfl

private theorem gal_nat {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {X Y : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of k)}
    {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y) (hu : u ≫ q = p) (σ : Ω ≃ₐ[k] Ω) :
    GlobalTheory.Et.galMap Ω p σ ≫ GlobalTheory.Et.geomMap Ω p u hu = GlobalTheory.Et.geomMap Ω p u hu ≫ GlobalTheory.Et.galMap Ω q σ := by
  have f1 : GlobalTheory.Et.geomMap Ω p u hu ≫ pullback.fst _ _ = pullback.fst _ _ ≫ u := pullback.lift_fst _ _ _
  have f2 : GlobalTheory.Et.geomMap Ω p u hu ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  apply pullback.hom_ext
  · rw [Category.assoc, f1, GlobalTheory.Et.galMap_fst_assoc, Category.assoc, GlobalTheory.Et.galMap_fst, f1]
  · rw [Category.assoc, f2, GlobalTheory.Et.galMap_snd, Category.assoc, GlobalTheory.Et.galMap_snd, ← Category.assoc, f2]

private theorem bc_range {R L M M' N : Type*} [CommRing R] [CommRing L] [Algebra R L] [AddCommGroup M] [AddCommGroup M']
    [AddCommGroup N] [Module R M] [Module R M'] [Module R N] (E : M →ₗ[R] N) (P : M' →ₗ[R] N)
    (h : ∀ m, E m ∈ LinearMap.range P) (w : L ⊗[R] M) : E.baseChange L w ∈ LinearMap.range (P.baseChange L) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    obtain ⟨n, hn⟩ := h m
    exact ⟨a ⊗ₜ n, by simp [hn]⟩
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hx hy

private theorem bc_sum {R L M N J : Type*} [CommRing R] [CommRing L] [Algebra R L] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (s : Finset J) (A : J → M →ₗ[R] N) (w : L ⊗[R] M) :
    (∑ j ∈ s, A j).baseChange L w = ∑ j ∈ s, (A j).baseChange L w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp [TensorProduct.tmul_sum]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, Finset.sum_add_distrib]

private theorem inv_mem (hV : VInv) (l : ℕ) [Fact l.Prime] {W Z : Scheme.{0}} (f : W ⟶ Z) (G : Type) [Group G] [Finite G]
    (b : G → (W ⟶ W)) (hG : IsGalois f G b) (L : Type) [Field L] [Algebra ℚ_[l] L] (y : L ⊗[ℚ_[l]] Htot l (sch.obj W))
    (hinv : ∀ δ, (pullTot l (sch.map (b δ))).baseChange L y = y) :
    y ∈ LinearMap.range ((pullTot l (sch.map f)).baseChange L) := by
  letI : Fintype G := Fintype.ofFinite G
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[l] L).injective
  have hmul : ∀ δ δ' m, pullTot l (sch.map (b δ')) (pullTot l (sch.map (b δ)) m) = pullTot l (sch.map (b (δ' * δ))) m := by
    intro δ δ' m
    rw [hG.2.2.2.2.1, Functor.map_comp, pullTot_comp]
    rfl
  have hE : ∀ m, (∑ δ, pullTot l (sch.map (b δ))) m ∈ LinearMap.range (pullTot l (sch.map f)) := fun m => by
    refine tot_range hV l _ G b hG _ fun δ' => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.sum_apply, map_sum]
    simp only [hmul]
    exact Fintype.sum_equiv (Equiv.mulLeft δ') _ _ fun _ => rfl
  have hEy : (∑ δ, pullTot l (sch.map (b δ))).baseChange L y = ((Fintype.card G : ℕ) : L) • y := by
    rw [bc_sum, Finset.sum_congr rfl fun δ _ => hinv δ, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hcard : ((Fintype.card G : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hy' : y = ((Fintype.card G : ℕ) : L)⁻¹ • (∑ δ, pullTot l (sch.map (b δ))).baseChange L y := by
    rw [hEy, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  rw [hy']
  exact Submodule.smul_mem _ _ (bc_range _ _ hE y)

private theorem empty_mem (l : ℕ) [Fact l.Prime] {W Z : Scheme.{0}} [IsEmpty ↑W] (f : W ⟶ Z) (hs : Surjective f) (L : Type)
    [Field L] [Algebra ℚ_[l] L] (y : L ⊗[ℚ_[l]] Htot l (sch.obj W)) :
    y ∈ LinearMap.range ((pullTot l (sch.map f)).baseChange L) := by
  haveI : IsEmpty ↑Z := ⟨fun z => by
    obtain ⟨w, -⟩ := hs.surj z
    exact isEmptyElim w⟩
  haveI : IsIso f := isIso_of_isEmpty _
  have hsur : ∀ m, (LinearMap.id : Htot l (sch.obj W) →ₗ[ℚ_[l]] _) m ∈ LinearMap.range (pullTot l (sch.map f)) := fun m => by
    refine ⟨pullTot l (sch.map (inv f)) m, ?_⟩
    have e : pullTot l (sch.map f) ∘ₗ pullTot l (sch.map (inv f)) = LinearMap.id := by
      rw [← pullTot_comp, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, pullTot_id]
    exact LinearMap.congr_fun e m
  have h2 := bc_range (L := L) _ _ hsur y
  rwa [LinearMap.baseChange_id, LinearMap.id_apply] at h2

theorem UpperTheory.Gal.Seam.pieceInS :
    GlobalTheory.GalV.VInv → HopEx → PieceIn := by
  intro hT hHop l _ K L _ _ H θ hN C hOn
  have hV := hT
  have hGK : IsGalois (UpperTheory.Gal.G3.piK C) C.Δ C.a := C.isGalois hOn
  have ha : ∀ δ, C.a δ ≫ H.q = H.q := fun δ => by
    rw [← UpperTheory.Gal.G3.piK_snd C, ← Category.assoc, hGK.2.2.2.2.2.choose δ]
  let g₀ : UpperTheory.Gal.G3.sp (PadicAlgCl l) ⟶ UpperTheory.Gal.G3.sp ↥K :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥K (PadicAlgCl l)))
  let b : C.Δ → (H.geomZ (PadicAlgCl l) ⟶ H.geomZ (PadicAlgCl l)) := fun δ => UpperTheory.Gal.G3.bcMap g₀ (C.a δ) (ha δ)
  have hG : IsGalois (toMod C) C.Δ b :=
    UpperTheory.Gal.G3.pBcGal (UpperTheory.Gal.G3.pBcSplits (UpperTheory.Gal.G3.pSplitsBasic (UpperTheory.Gal.G3.pSplitsPts UpperTheory.Gal.G3.pIsoPts)
      UpperTheory.Gal.G3.pPtsOfSplits)) g₀ _ _ (UpperTheory.Gal.G3.piK C) (UpperTheory.Gal.G3.piK_snd C) C.Δ C.a ha hGK
  refine ⟨?_, ?_, fun σ => ?_⟩
  · rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (tot_inj hV l _ C.Δ b hG)
  · intro y hy
    by_cases hZ : Nonempty ↑(H.geomZ (PadicAlgCl l))
    · have hop' : ∀ δ, ∃ g, hop l H (PadicAlgCl l) g = pullTot l (sch.map (b δ)) ∧ θ g = 1 := fun δ => by
        obtain ⟨g, hiso, ht, hθ⟩ := C.fix δ
        haveI : IsIso (H.sΩ (PadicAlgCl l) g) := GlobalTheory.GalV.GaloisTowerConditions.geomMap_isIso (PadicAlgCl l) (H.s g) rfl
        have b1 : b δ ≫ pullback.fst H.q g₀ = pullback.fst H.q g₀ ≫ C.a δ := UpperTheory.Gal.G3.bcMap_fst g₀ (C.a δ) (ha δ)
        have b2 : b δ ≫ pullback.snd H.q g₀ = pullback.snd H.q g₀ := UpperTheory.Gal.G3.bcMap_snd g₀ (C.a δ) (ha δ)
        have t' : H.tΩ (PadicAlgCl l) g = UpperTheory.Gal.G3.bcMap g₀ (H.t g) (H.comm g) := rfl
        have s' : H.sΩ (PadicAlgCl l) g = UpperTheory.Gal.G3.bcMap g₀ (H.s g) rfl := rfl
        have e : H.tΩ (PadicAlgCl l) g = H.sΩ (PadicAlgCl l) g ≫ b δ := by
          rw [t', s']
          apply pullback.hom_ext
          · rw [UpperTheory.Gal.G3.bcMap_fst, Category.assoc, b1, ← Category.assoc, UpperTheory.Gal.G3.bcMap_fst, Category.assoc, ht]
          · rw [UpperTheory.Gal.G3.bcMap_snd, Category.assoc, b2, UpperTheory.Gal.G3.bcMap_snd]
        have hc := hHop l ↥K (PadicAlgCl l) H hN g
        rw [e] at hc
        exact ⟨g, corr_iso hV l (H.sΩ (PadicAlgCl l) g) (b δ) _ hc, hθ⟩
      have hinv : ∀ δ, (pullTot l (sch.map (b δ))).baseChange L y = y := fun δ => by
        obtain ⟨g, e, hθ⟩ := hop' δ
        have h1 := Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hy g)
        rw [hθ, one_smul, e] at h1
        exact h1
      exact inv_mem hV l _ C.Δ b hG L y hinv
    · haveI : IsEmpty ↑(H.geomZ (PadicAlgCl l)) := not_nonempty_iff.1 hZ
      exact empty_mem l _ hG.2.2.1 L y
  · change pullTot l (sch.map _) ∘ₗ pullTot l (sch.map _) = pullTot l (sch.map _) ∘ₗ pullTot l (sch.map _)
    rw [← pullTot_comp, ← pullTot_comp, ← Functor.map_comp, ← Functor.map_comp]
    congr 2
    exact gal_nat _ _ σ
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.SubAdm
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace UpperTheory.Gal.Seam

variable {l : ℕ} [Fact l.Prime]

private theorem isAdmP_block (P : LocPrime l) (G : Subgroup (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l)) {N D : ℕ} {a : Fin N → ℕ}
    (e : (Σ n, Fin (a n)) ≃ Fin D) (R : ∀ n, G → Matrix (Fin (a n)) (Fin (a n)) ℚ_[l])
    (h : ∀ n, IsAdmP P G (R n)) :
    IsAdmP P G (fun σ => (Matrix.blockDiagonal' fun n => R n σ).submatrix e.symm e.symm) := by
  choose A B hm hAB hσ using h
  have hz : (0 : P.R.BdR) ∈ Set.range P.ιB := ⟨0, map_zero _⟩
  have hmem : ∀ (C : ∀ n, Matrix (Fin (a n)) (Fin (a n)) P.R.BdR), (∀ n i j, C n i j ∈ Set.range P.ιB) →
      ∀ s t, Matrix.blockDiagonal' C s t ∈ Set.range P.ιB := by
    intro C hC s t
    rw [Matrix.blockDiagonal'_apply]
    split_ifs with hst
    · exact hC _ _ _
    · exact hz
  refine ⟨(Matrix.blockDiagonal' A).submatrix e.symm e.symm, (Matrix.blockDiagonal' B).submatrix e.symm e.symm,
    fun i j => ⟨hmem A (fun n i j => (hm n i j).1) _ _, hmem B (fun n i j => (hm n i j).2) _ _⟩, ?_, fun σ => ?_⟩
  · rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul]
    simp only [hAB]
    exact (congrArg (fun X => Matrix.submatrix X e.symm e.symm) (Matrix.blockDiagonal'_one (m' := fun n => Fin (a n)))).trans
      (Matrix.submatrix_one_equiv _)
  · rw [← Matrix.submatrix_map, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv,
      Matrix.blockDiagonal'_map _ _ (map_zero _), Matrix.blockDiagonal'_map _ _ (map_zero _),
      ← Matrix.blockDiagonal'_mul]
    simp only [hσ]

end UpperTheory.Gal.Seam


open UpperTheory.Gal.Seam in
theorem UpperTheory.Gal.Seam.subAdm : UpperTheory.Gal.Seam.SubAdm := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw N d a R r hR M hM hint
  let D := Fintype.card (Σ n, Fin (a n))
  let e : (Σ n, Fin (a n)) ≃ Fin D := Fintype.equivFin _
  let f : ↥(GK Bw.Kw) →* Matrix (Fin D) (Fin D) ℚ_[l] :=
    { toFun := fun σ => (Matrix.blockDiagonal' fun n => R n σ).submatrix e.symm e.symm
      map_one' := by
        simp only [fun n => (hR n).1]
        exact (congrArg (fun X => Matrix.submatrix X e.symm e.symm) (Matrix.blockDiagonal'_one (m' := fun n => Fin (a n)))).trans
          (Matrix.submatrix_one_equiv _)
      map_mul' := fun σ τ => by
        rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul]
        simp only [fun n => (hR n).2.1 σ τ] }
  let ρ : ↥(GK Bw.Kw) →* GL (Fin D) ℚ_[l] := f.toHomUnits
  have hρf : ∀ σ, (ρ σ : Matrix (Fin D) (Fin D) ℚ_[l]) = f σ := fun σ => MonoidHom.coe_toHomUnits f σ
  have hadm : IsAdmP P (GK Bw.Kw) (fun σ => (ρ σ : Matrix (Fin D) (Fin D) ℚ_[l])) := by
    have h0 : (fun σ => (ρ σ : Matrix (Fin D) (Fin D) ℚ_[l])) =
        fun σ => (Matrix.blockDiagonal' fun n => R n σ).submatrix e.symm e.symm := funext hρf
    rw [h0]
    exact isAdmP_block P (GK Bw.Kw) e R (fun n => (hR n).2.2)
  let L : FinExt l := Bw.LL
  haveI := L.2
  let r' : ↥(GK Bw.Kw) →* GL (Fin D) ↥L.1 :=
    (Units.map (RingHom.mapMatrix (algebraMap ℚ_[l] ↥L.1)).toMonoidHom).comp ρ
  have hr' : ∀ σ i j, (r' σ).val i j = algebraMap ℚ_[l] ↥L.1 ((ρ σ).val i j) := fun σ i j => rfl
  obtain ⟨T⟩ := hT
  have hc := isCrys_of_isAdmP l P AI T Bw.Kw L D ρ r' hr' hadm
  have hcρ : WeaklyAdmissibleFiltrations.IsCrys (P.PD Bw.Kw) (((Matrix.toLinAlgEquiv' : Matrix (Fin D) (Fin D) ℚ_[l] ≃ₐ[ℚ_[l]] _) : _ →* _).comp
      ((Units.coeHom _).comp ρ) : Representation ℚ_[l] ↥(GK Bw.Kw) (Fin D → ℚ_[l])) :=
    (GlobalTheory.Pst.isCrys_ext_iff (P.PD Bw.Kw) (fun g => ⟨(ρ g : Matrix (Fin D) (Fin D) ℚ_[l]), fun x => rfl, fun x => rfl⟩)).1 hc
  refine GlobalTheory.CrysSubRep.isCrysAt_of_sub l P AI ⟨T⟩ E Ω Gw O Bw D d ρ r hcρ (M.submatrix e.symm id) ?_ ?_
  · intro x y hxy
    refine hM (funext fun s => ?_)
    have := congrFun hxy (e s)
    simpa [Matrix.mulVec, dotProduct] using this
  · intro g
    have h1 := hint g
    have h3 : (ρ (Bw.e g) : Matrix (Fin D) (Fin D) ℚ_[l]) =
        (Matrix.blockDiagonal' fun n => R n (Bw.e g)).submatrix e.symm e.symm := hρf _
    rw [h3]
    have h2 : (M.submatrix e.symm id) * (r g : Matrix (Fin d) (Fin d) (Om l)) =
        (M * (r g : Matrix (Fin d) (Fin d) (Om l))).submatrix e.symm id := Matrix.ext fun _ _ => rfl
    rw [h2, ← h1]
    rw [← Matrix.submatrix_map, Matrix.submatrix_mul_equiv]
end
end

