module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetCore
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.CotangentIndependentOfResidues
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem det_mem_annihilator_of_relations {B N ι : Type} [CommRing B] [AddCommGroup N] [Module B N] [Fintype ι] [DecidableEq ι]
    (z : Matrix ι ι B) (n : ι → N) (hspan : Submodule.span B (Set.range n) = ⊤)
    (hrel : ∀ i, ∑ j, z i j • n j = 0) : z.det ∈ Module.annihilator B N := by
  have h1 : ∀ k, z.det • n k = 0 := by
    intro k
    have h2 : ∑ i, z.adjugate k i • ∑ j, z i j • n j = 0 := by simp [hrel]
    have h3 : ∑ i, z.adjugate k i • ∑ j, z i j • n j = ∑ j, (z.adjugate * z) k j • n j := by
      simp only [Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, mul_smul]
      exact Finset.sum_comm
    rw [h3, Matrix.adjugate_mul] at h2
    simpa [Matrix.one_apply, ite_smul] using h2
  rw [Module.mem_annihilator]
  intro x
  have hx : x ∈ Submodule.span B (Set.range n) := hspan ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact h1 k
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_comm, hx, smul_zero]

private theorem cotangent_independent_of_residues (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (hϖ : Irreducible ϖ) (D0 g : ℕ) (c : Fin g × Fin g → Fin D0 → O)
    (hc : LinearIndependent (ResidueField O) (fun p a => residue O (c p a)))
    (w : Fin g × Fin g → MvPowerSeries (Fin D0 ⊕ Fin g) O)
    (hw : ∀ p, w p ∈ Ideal.span {(MvPowerSeries.C ϖ : MvPowerSeries (Fin D0 ⊕ Fin g) O)} ⊔ maximalIdeal _ ^ 2) :
    CotInd (MvPowerSeries (Fin D0 ⊕ Fin g) O)
      (Sum.elim (fun p : Fin g × Fin g =>
          (∑ a, MvPowerSeries.C (c p a) * MvPowerSeries.X (Sum.inl a)) - w p)
        (fun j : Fin g => MvPowerSeries.X (Sum.inr j))) := by
  obtain ⟨-, -, hx⟩ := mvPowerSeries_cotInd O ϖ hϖ (Fin D0 ⊕ Fin g)
  have hw' : ∀ p, ∃ u s, s ∈ maximalIdeal (MvPowerSeries (Fin D0 ⊕ Fin g) O) ^ 2 ∧
      w p = u * MvPowerSeries.C ϖ + s := by
    intro p
    obtain ⟨y, hy, s, hs, h⟩ := Submodule.mem_sup.1 (hw p)
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    exact ⟨u, s, hs, h.symm⟩
  choose u s hs hus using hw'
  refine ⟨?_, fun b hb => ?_⟩
  · rintro (p | j)
    · refine sub_mem (Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (hx.mem (some (Sum.inl a)))) ?_
      rw [hus]
      exact add_mem (Ideal.mul_mem_left _ _ (hx.mem none)) (Ideal.pow_le_self two_ne_zero (hs p))
    · exact hx.mem (some (Sum.inr j))
  · have h1 : ∑ p, b (Sum.inl p) * s p ∈ maximalIdeal (MvPowerSeries (Fin D0 ⊕ Fin g) O) ^ 2 :=
      Ideal.sum_mem _ fun p _ => Ideal.mul_mem_left _ _ (hs p)
    have h2 := hx.indep (fun o => o.elim (-∑ p, b (Sum.inl p) * u p)
      (Sum.elim (fun a => ∑ p, b (Sum.inl p) * MvPowerSeries.C (c p a)) (fun j => b (Sum.inr j)))) (by
        have h3 := add_mem hb h1
        convert h3 using 1
        simp only [Fintype.sum_option, Fintype.sum_sum_type, Option.elim, Sum.elim_inl, Sum.elim_inr, hus,
          Finset.sum_mul, mul_sub, mul_add, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
          neg_mul, mul_assoc]
        rw [Finset.sum_comm]
        ring)
    rintro (p | j)
    · rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff, ← residue_eq_zero_iff]
      refine Fintype.linearIndependent_iff.1 hc
        (fun p => residue O (MvPowerSeries.constantCoeff (b (Sum.inl p)))) ?_ p
      funext a
      have h4 := h2 (some (Sum.inl a))
      rw [GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff, ← residue_eq_zero_iff] at h4
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [Finset.sum_apply, map_sum, map_mul] using h4
    · exact h2 (some (Sum.inr j))

theorem UpperTheory.V.Pa.presOut1 :
    ∀ (O B A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CommRing B] [Algebra O B] [IsCO O B] [CommRing A] [Algebra B A] [Module.Finite B A] (N : Submodule B A), Function.Injective (algebraMap B A) → _root_.IsCompl (1 : Submodule B A) N → (∀ a ∈ N, ∀ b ∈ N, ∃ c ∈ maximalIdeal B, a * b = algebraMap B A c) → ∀ (D0 g : ℕ) (X : Fin D0 → B) (m : Fin g → N) (c : Fin g × Fin g → Fin D0 → O), (∀ a, X a ∈ maximalIdeal B) → Submodule.span B (Set.range m) = ⊤ → LinearIndependent (ResidueField O) (fun p a => residue O (c p a)) → maximalIdeal B ≤ Ideal.span (Set.range X) ⊔ ((maximalIdeal O).map (algebraMap O B) ⊔ maximalIdeal B ^ 2 ⊔ ired N) → (∀ i, ∑ j, (∑ a, algebraMap O B (c (i, j) a) * X a) • m j ∈ ((maximalIdeal O).map (algebraMap O B) ⊔ maximalIdeal B ^ 2 ⊔ ired N) • (⊤ : Submodule B N)) → ∀ Z Q : Ideal B, Z.IsPrime → Q.IsPrime → ((1 + D0 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (B ⧸ Z) → ¬ ired N ≤ Z → (¬ ired N ≤ Q ∨ Module.annihilator B N ≤ Q) → Z ≤ Q := by
  intro O B A _ _ _ _ _ _ _ _ _ _ N hinj hcompl hmul D0 g X m c hX hm hc hg hr Z Q hZ hQ hd hZr hQr
  letI : Algebra O A := ((algebraMap B A).comp (algebraMap O B)).toAlgebra
  haveI : IsScalarTower O B A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨hA, hmA, hired⟩ := aaCO O B A N hinj hcompl hmul
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmO : maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  obtain ⟨hreg, hdim, hx⟩ := mvPowerSeries_cotInd O ϖ hϖ (Fin D0 ⊕ Fin g)
  haveI := co_mvps O O (Fin D0 ⊕ Fin g)
  have hBA : (maximalIdeal B).map (algebraMap B A) ≤ maximalIdeal A := fun a ha =>
    (hmA a).2 (Ideal.mem_sup_left ha)
  obtain ⟨F, ⟨hC, hF⟩, -⟩ := co_ev O O A (Fin D0 ⊕ Fin g) (Algebra.ofId O A)
    (Sum.elim (fun a => algebraMap B A (X a)) (fun j => (m j : A))) (by
      rintro (a | j)
      · exact hBA (Ideal.mem_map_of_mem _ (hX a))
      · exact (hmA _).2 (Ideal.mem_sup_right (Ideal.subset_span (m j).2)))
  have hC' : ∀ x, F (MvPowerSeries.C x) = algebraMap B A (algebraMap O B x) := hC
  have hF1 : ∀ a, F (MvPowerSeries.X (Sum.inl a)) = algebraMap B A (X a) := fun a => hF (Sum.inl a)
  have hF2 : ∀ j, F (MvPowerSeries.X (Sum.inr j)) = (m j : A) := fun j => hF (Sum.inr j)
  have hNI : ∀ I : Ideal A, (∀ j, (m j : A) ∈ I) → ∀ y ∈ N, y ∈ I := by
    intro I hI y hy
    have hy' : (⟨y, hy⟩ : N) ∈ Submodule.span B (Set.range m) := hm ▸ Submodule.mem_top
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun B).1 hy'
    have : y = ∑ j, b j • (m j : A) := by
      have := congrArg Subtype.val hb
      simpa using this.symm
    rw [this]
    exact Ideal.sum_mem _ fun j _ => by
      rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ (hI j)
  have hJ : ((maximalIdeal O).map (algebraMap O B) ⊔ maximalIdeal B ^ 2 ⊔ ired N).map (algebraMap B A) ≤
      (Ideal.span {(MvPowerSeries.C ϖ : MvPowerSeries (Fin D0 ⊕ Fin g) O)}).map F ⊔ maximalIdeal A ^ 2 := by
    rw [Ideal.map_sup, Ideal.map_sup]
    refine sup_le (sup_le (le_sup_of_le_left ?_) (le_sup_of_le_right ?_)) (le_sup_of_le_right hired)
    · rw [hmO, Ideal.map_span, Ideal.map_span, Ideal.map_span]
      simp [hC']
    · rw [Ideal.map_pow]
      exact Ideal.pow_right_mono hBA 2
  have hcot : maximalIdeal A ≤ (maximalIdeal (MvPowerSeries (Fin D0 ⊕ Fin g) O)).map F ⊔ maximalIdeal A ^ 2 := by
    refine le_trans (fun a ha => (hmA a).1 ha) (sup_le ?_ ?_)
    · refine (Ideal.map_mono hg).trans ?_
      rw [Ideal.map_sup]
      refine sup_le (le_sup_of_le_left ?_) (hJ.trans (sup_le_sup_right (Ideal.map_mono ?_) _))
      · rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
        rintro _ ⟨a, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_comap, ← hF1]
        exact Ideal.mem_map_of_mem _ (hx.mem (some (Sum.inl a)))
      · rw [Ideal.span_singleton_le_iff_mem]
        exact hx.mem none
    · refine le_sup_of_le_left (Ideal.span_le.2 fun y hy => hNI _ (fun j => ?_) y hy)
      rw [← hF2]
      exact Ideal.mem_map_of_mem _ (hx.mem (some (Sum.inr j)))
  have hsurj : Function.Surjective F := co_surj O _ A F hcot
  have hmP : maximalIdeal A ≤ (maximalIdeal (MvPowerSeries (Fin D0 ⊕ Fin g) O)).map F := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A)
      (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    rwa [smul_eq_mul, ← pow_two]
  have hw : ∀ i, ∃ w : Fin g → B,
      (∀ j, w j ∈ (maximalIdeal O).map (algebraMap O B) ⊔ maximalIdeal B ^ 2 ⊔ ired N) ∧
      ∑ j, w j • m j = ∑ j, (∑ a, algebraMap O B (c (i, j) a) * X a) • m j := by
    intro i
    have h := hr i
    rw [← hm, Submodule.mem_ideal_smul_span_iff_exists_sum] at h
    obtain ⟨a, ha, h⟩ := h
    refine ⟨a, ha, ?_⟩
    rw [← h, Finsupp.sum_fintype _ _ (by simp)]
  choose w hwJ hwe using hw
  have hw2 : ∀ p : Fin g × Fin g, ∃ v ∈ Ideal.span {(MvPowerSeries.C ϖ : MvPowerSeries (Fin D0 ⊕ Fin g) O)} ⊔
      maximalIdeal _ ^ 2, F v = algebraMap B A (w p.1 p.2) := by
    intro p
    refine (Ideal.mem_map_iff_of_surjective F hsurj).1 ?_
    rw [Ideal.map_sup, Ideal.map_pow]
    exact sup_le_sup_left (Ideal.pow_right_mono hmP 2) _ (hJ (Ideal.mem_map_of_mem _ (hwJ p.1 p.2)))
  choose v hv hFv using hw2
  let ζ : Matrix (Fin g) (Fin g) B := Matrix.of fun i j => (∑ a, algebraMap O B (c (i, j) a) * X a) - w i j
  let z : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin D0 ⊕ Fin g) O) := Matrix.of fun i j =>
    (∑ a, MvPowerSeries.C (c (i, j) a) * MvPowerSeries.X (Sum.inl a)) - v (i, j)
  have hζ : ∀ i, ∑ j, ζ i j • m j = 0 := by
    intro i
    simp only [ζ, Matrix.of_apply, sub_smul, Finset.sum_sub_distrib, hwe, sub_self]
  have hzζ : ∀ i j, F (z i j) = algebraMap B A (ζ i j) := by
    intro i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [z, ζ, Matrix.of_apply, map_sub, map_sum, map_mul, hC', hF1, hFv]
  have hann := det_mem_annihilator_of_relations ζ m hm hζ
  have hdetQ : ζ.det ∈ Q := by
    rcases hQr with h | h
    · by_contra hn
      apply h
      rw [ired, Ideal.span_le]
      rintro b ⟨x, hx, y, hy, hxy⟩
      refine (hQ.mem_or_mem (x := ζ.det) ?_).resolve_left hn
      have h0 : ζ.det • x = 0 := congrArg Subtype.val (Module.mem_annihilator.1 hann ⟨x, hx⟩)
      have : ζ.det * b = 0 := hinj (by
        rw [map_mul, ← hxy, ← mul_assoc, ← Algebra.smul_def, h0, zero_mul, map_zero])
      rw [this]
      exact Q.zero_mem
    · exact h hann
  haveI : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).2 hinj
  obtain ⟨Q', -, hQ', hQQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral Q (⊥ : Ideal A) (by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    have : x = 0 := hinj (by rw [hx, map_zero])
    rw [this]
    exact Q.zero_mem)
  rw [← hQQ]
  refine under_le_of_det_mem _ (Fin g) z (fun j => MvPowerSeries.X (Sum.inr j))
    (cotangent_independent_of_residues O ϖ hϖ D0 g c hc v hv) B A (F : _ →+* A) hsurj ?_ Z hZ ?_ ?_ Q' hQ' ?_
  · rw [relIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    show F (∑ j, z i j * MvPowerSeries.X (Sum.inr j)) = 0
    have := congrArg Subtype.val (hζ i)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hzζ, hF2, ← Algebra.smul_def]
    simpa using this
  · rw [hdim]
    refine le_trans (le_of_eq ?_) (add_le_add_left hd _)
    simp only [Fintype.card_sum, Fintype.card_fin]
    rw [← Nat.cast_add]
    congr 1
    omega
  · intro Z' hZ' hZZ
    by_contra hn
    push Not at hn
    apply hZr
    rw [ired, Ideal.span_le]
    rintro b ⟨x, hx, y, hy, hxy⟩
    rw [← hZZ]
    show algebraMap B A b ∈ Z'
    rw [← hxy]
    exact Ideal.mul_mem_left _ _ (hNI Z' (fun j => hF2 j ▸ hn j) y hy)
  · have : (F : MvPowerSeries (Fin D0 ⊕ Fin g) O →+* A) z.det = algebraMap B A ζ.det := by
      rw [RingHom.map_det, RingHom.map_det]
      congr 1
      ext i j
      exact hzζ i j
    rw [this]
    rw [← hQQ] at hdetQ
    exact hdetQ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EvenCocyclesLiftLaurent
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.k2F :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), K2 h k → EvenCocyclesLiftLaurent h k := by
  intro l _ L G G0 h n x k hK z hz
  set f := algebraMap x.A x.Fr with hf
  have ht : f x.t ≠ 0 := by
    intro h0
    apply PowerSeries.X_ne_zero (R := x.K)
    exact IsFractionRing.injective x.A x.Fr (h0.trans (map_zero f).symm)
  choose s₀ hs using fun i j => selScale l L G G0 h n x true (z i j) (hz i j).1 (hz i j).2
  set S := Finset.univ.sup (fun p : Fin (k.g + 1) × Fin k.g => s₀ p.1 p.2) with hSdef
  have hS : ∀ i j, s₀ i j ≤ S := fun i j =>
    Finset.le_sup (f := fun p : Fin (k.g + 1) × Fin k.g => s₀ p.1 p.2) (Finset.mem_univ (i, j))
  choose z' hz' hzz using fun i j => hs i j S (hS i j)
  obtain ⟨c, hc, Ψ, hΨ, hΨe⟩ := hK z' (fun i j => hz' i j)
  obtain ⟨hΨ1, hΨ2⟩ := selMap2 l L G G0 h n x k Ψ hΨ
  refine ⟨fun i => f (c i) * f x.t ^ S, ?_, _, hΨ1, hΨ2, ?_⟩
  · intro h0
    apply hc
    funext i
    have e := congrFun h0 i
    rcases mul_eq_zero.1 e with e | e
    · exact IsFractionRing.injective x.A x.Fr (e.trans (map_zero f).symm)
    · exact absurd e (pow_ne_zero S ht)
  · intro j γ a b
    have hz2 : ∀ i, f (z' i j γ a b) = f x.t ^ S * z i j γ a b := fun i => by
      have e := congrArg (fun M => M a b) (hzz i j γ)
      simpa using e
    show f ((Ψ γ a b).ep' j) = _
    rw [hΨe j γ a b]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.sum_apply, Finset.sum_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
      map_sum, map_mul, hz2]
    refine Finset.sum_congr rfl fun i _ => by ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PhDecDApply
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private noncomputable def UpperTheory.V.Pa.phDecD {l : ℕ} [Fact l.Prime] (S : Ctx l) (Φ : S.U.N →+ S.F) (y : S.U.N) : S.Bh →+ S.F where
  toFun b := Φ (b • y) - S.rF b * Φ y
  map_zero' := by simp
  map_add' b b' := by rw [add_smul, map_add (f := _), map_add (f := _)]; ring

private theorem UpperTheory.V.Pa.phDecD_apply {l : ℕ} [Fact l.Prime] (S : Ctx l) (Φ : S.U.N →+ S.F) (y : S.U.N) (b : S.Bh) :
    phDecD S Φ y b = Φ (b • y) - S.rF b * Φ y := rfl

private theorem UpperTheory.V.Pa.phDecD_mem {l : ℕ} [Fact l.Prime] (S : Ctx l) (Φ : S.U.N →+ S.F) (hΦ : Φ ∈ S.Ph)
    (y : S.U.N) : phDecD S Φ y ∈ S.Tp := by
  obtain ⟨h1, h2⟩ := hΦ
  have hm : ∀ q ∈ maximalIdeal S.Bh, S.rF q = 0 := fun q hq => by
    rw [← S.rF_ker] at hq; exact hq
  have dec : ∀ b : S.Bh, ∃ (o : S.OO) (q : S.Bh), q ∈ maximalIdeal S.Bh ∧ b = algebraMap S.OO S.Bh o + q := by
    intro b
    obtain ⟨o, ho⟩ := S.oo_surj (S.rF b)
    refine ⟨o, b - algebraMap S.OO S.Bh o, ?_, by ring⟩
    rw [← S.rF_ker, RingHom.mem_ker, map_sub, ← ho]
    simp
  refine ⟨fun b b' => ?_, fun o => ?_, fun b hb => ?_⟩
  · obtain ⟨o, q, hq, rfl⟩ := dec b
    obtain ⟨o', q', hq', rfl⟩ := dec b'
    have hqq : q * q' ∈ S.J2 := by
      refine Ideal.mem_sup_left (Ideal.mem_sup_right ?_)
      rw [pow_two]
      exact Ideal.mul_mem_mul hq hq'
    have e : ((algebraMap S.OO S.Bh o + q) * (algebraMap S.OO S.Bh o' + q')) • y =
        algebraMap S.OO S.Bh o • (algebraMap S.OO S.Bh o' • y) + algebraMap S.OO S.Bh o • (q' • y) +
          algebraMap S.OO S.Bh o' • (q • y) + (q * q') • y := by
      simp only [smul_smul, ← add_smul]
      congr 1
      ring
    simp only [phDecD_apply]
    rw [e]
    simp only [add_smul, map_add (f := _), map_mul, h1, h2 _ hqq, hm q hq, hm q' hq']
    ring
  · rw [phDecD_apply, h1, sub_self]
  · have hi : ired S.U.N ≤ maximalIdeal S.Bh := by
      refine Ideal.span_le.2 ?_
      rintro a ⟨x, hx, z, hz, e⟩
      obtain ⟨c, hc, e'⟩ := S.U.mul_mem x hx z hz
      have : a = c := S.U.inj (e.symm.trans e')
      rw [this]
      exact hc
    rw [phDecD_apply, h2 b (Ideal.mem_sup_right hb), hm b (hi hb)]
    simp

private theorem UpperTheory.V.Pa.phDec_expand {F A : Type} [Field F] [AddCommGroup A] (T : Submodule F (A →+ F)) {e : ℕ}
    (v : Module.Basis (Fin e) F T) (d : T) (b : A) :
    (d : A →+ F) b = ∑ k, (v k : A →+ F) b * v.coord k d := by
  let ev : T →ₗ[F] F :=
    { toFun := fun α => (α : A →+ F) b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change ev d = ∑ k, ev (v k) * v.coord k d
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← v.sum_repr d, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm, Module.Basis.coord_apply]

theorem UpperTheory.V.Pa.phDec :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ Φ ∈ S.Ph, ∃ (e : ℕ) (α : Fin e → S.Bh →+ S.F) (μ : Fin e → S.U.N →+ S.F), (∀ k, α k ∈ S.Tp) ∧ (∀ k, μ k ∈ S.La) ∧ ∀ (b : S.Bh) y, Φ (b • y) = S.rF b * Φ y + ∑ k, α k b * μ k y := by
  intro l _ S Φ hΦ
  have : Module.Finite S.F S.Tp := (tpDual l S).1
  let v := Module.finBasis S.F S.Tp
  let D : S.U.N →+ S.Tp :=
    { toFun := fun y => ⟨phDecD S Φ y, phDecD_mem S Φ hΦ y⟩
      map_zero' := by
        refine Subtype.ext (AddMonoidHom.ext fun b => ?_)
        simp [phDecD_apply]
      map_add' := fun y y' => by
        refine Subtype.ext (AddMonoidHom.ext fun b => ?_)
        simp only [Submodule.coe_add, AddMonoidHom.add_apply, phDecD_apply, smul_add, map_add (f := _)]
        ring }
  have hD : ∀ y b, (D y : S.Bh →+ S.F) b = Φ (b • y) - S.rF b * Φ y := fun _ _ => rfl
  have hs : ∀ (c : S.Bh) y, D (c • y) = S.rF c • D y := by
    intro c y
    refine Subtype.ext (AddMonoidHom.ext fun b => ?_)
    have := (D y).2.1 b c
    rw [hD, hD, hD, map_mul] at this
    rw [Submodule.coe_smul, AddMonoidHom.smul_apply, hD, hD, smul_smul, smul_eq_mul]
    linear_combination this
  refine ⟨_, fun k => v k, fun k => (v.coord k).toAddMonoidHom.comp D, fun k => (v k).2, fun k c y => ?_,
    fun b y => ?_⟩
  · change v.coord k (D (c • y)) = S.rF c * v.coord k (D y)
    rw [hs, map_smul, smul_eq_mul]
  · have := phDec_expand S.Tp v (D y) b
    rw [hD] at this
    change Φ (b • y) = S.rF b * Φ y + ∑ k, (v k : S.Bh →+ S.F) b * v.coord k (D y)
    rw [← this]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelmerRankBoundLaurent
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem dual_numbers_map_smul {X Y : Type} [CommRing X] [CommRing Y] {g : ℕ} (f : X →+* Y) (c : X) (u : DD X g) :
    DD.map f (c • u) = f c • DD.map f u := by
  show DD.map f (DD.C c * u) = DD.C (f c) * DD.map f u
  rw [map_mul]
  congr 1
  apply DD.ext
  · rfl
  · funext j
    exact map_zero f
  · funext j
    exact map_zero f
  · exact map_zero f

private theorem map_first_order_lift_residue_field {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (g : F.G₀) :
    (DD.map (algebraMap x.A x.Fr)).mapMatrix (k.ρ1 x.A g) = k.ρ1 x.Fr g := by
  have hE : (DD.map (algebraMap x.A x.Fr)).mapMatrix (DD.epM fun j => (k.κ j g).map (algebraMap x.A x.A))
      = DD.epM fun j => (k.κ j g).map (algebraMap x.A x.Fr) := by
    ext a b <;> simp [DD.epM, DD.map, RingHom.mapMatrix_apply]
  have hR : (DD.map (algebraMap x.A x.Fr)).mapMatrix (x.ρX (DD x.A k.g) g) = x.ρX (DD x.Fr k.g) g := by
    ext a b <;> simp [NP.ρX, DD.map, RingHom.mapMatrix_apply]
    all_goals first | rfl | exact map_zero _
  unfold Kap.ρ1
  rw [map_mul, map_add (f := _), map_one, hE, hR]

private theorem map_mem_dual_numbers_part {A Y : Type} [CommRing A] [CommRing Y] [Algebra A Y] {g : ℕ} {b1 b2 b3 b4 : Bool} {u : DD A g}
    (hu : u ∈ ddPart A A g b1 b2 b3 b4) : DD.map (algebraMap A Y) u ∈ ddPart A Y g b1 b2 b3 b4 := by
  obtain ⟨h1, h2, h3, h4⟩ := hu
  refine ⟨fun hb => ?_, fun hb => ?_, fun hb => ?_, fun hb => ?_⟩
  · show algebraMap A Y u.a = 0
    rw [h1 hb, map_zero]
  · show (fun j => algebraMap A Y (u.ep j)) = 0
    rw [h2 hb]
    funext j
    simp
  · show (fun j => algebraMap A Y (u.ep' j)) = 0
    rw [h3 hb]
    funext j
    simp
  · show algebraMap A Y u.eta = 0
    rw [h4 hb, map_zero]

theorem UpperTheory.V.Pa.k1F :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ D0, K1 h k D0 → SelmerRankBoundLaurent h k D0 := by
  intro l _ L G G0 h n x k D0 hK e z hz hind
  classical
  choose s₀ hs₀ using fun i => selScale1 l L G G0 h n x k (z i) (hz i).1 (hz i).2
  obtain ⟨z', hz'S, hz'map⟩ : ∃ z' : Fin e → G.frame.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g),
      (∀ i, z' i ∈ Sel1 h x.A k) ∧ ∀ i g, (z' i g).map (DD.map (algebraMap x.A x.Fr))
        = (algebraMap x.A x.Fr) x.t ^ (Finset.univ.sup s₀) • z i g := by
    choose z' hz'S hz'map using fun i => hs₀ i (Finset.univ.sup s₀) (Finset.le_sup (Finset.mem_univ i))
    exact ⟨z', hz'S, hz'map⟩
  apply hK e z' hz'S
  intro c hc
  obtain ⟨Y, hY, hYt, hYeq⟩ := hc
  have hmapSmul : ∀ (c0 : x.A) (M : Matrix (Fin n) (Fin n) (DD x.A k.g)),
      (DD.map (algebraMap x.A x.Fr)).mapMatrix (c0 • M)
        = algebraMap x.A x.Fr c0 • (DD.map (algebraMap x.A x.Fr)).mapMatrix M := by
    intro c0 M
    exact Matrix.ext fun a b => dual_numbers_map_smul (algebraMap x.A x.Fr) c0 (M a b)
  have key : ∑ i, (algebraMap x.A x.Fr (c i) * algebraMap x.A x.Fr x.t ^ (Finset.univ.sup s₀)) • z i
      ∈ Bd1 h x.Fr k := by
    simp only [Bd1, Bd, Set.mem_setOf_eq]
    refine ⟨(DD.map (algebraMap x.A x.Fr)).mapMatrix Y, ?_, ?_, ?_⟩
    · intro a b
      exact ⟨fun hab => map_mem_dual_numbers_part ((hY a b).1 hab), fun hab => map_mem_dual_numbers_part ((hY a b).2 hab)⟩
    · refine Matrix.ext fun a b => ?_
      show DD.map (algebraMap x.A x.Fr) (Y b a) = -(DD.map (algebraMap x.A x.Fr) (Y a b))
      rw [← map_neg]
      congr 1
      exact congrFun (congrFun hYt a) b
    · funext g
      have h1 := congrFun hYeq g
      have hsum : (DD.map (algebraMap x.A x.Fr)).mapMatrix (∑ i, c i • z' i g)
          = ∑ i, (algebraMap x.A x.Fr (c i) * algebraMap x.A x.Fr x.t ^ (Finset.univ.sup s₀)) • z i g := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hmapSmul, show (DD.map (algebraMap x.A x.Fr)).mapMatrix (z' i g)
          = algebraMap x.A x.Fr x.t ^ (Finset.univ.sup s₀) • z i g from hz'map i g, smul_smul]
      simp only [Finset.sum_apply, Pi.smul_apply] at h1 ⊢
      rw [← hsum, h1]
      simp only [dY, map_sub, map_mul, map_first_order_lift_residue_field]
  have hc' := hind _ key
  have ht : algebraMap x.A x.Fr x.t ≠ 0 := fun h0 =>
    PowerSeries.X_ne_zero ((IsFractionRing.injective x.A x.Fr) (h0.trans (map_zero _).symm))
  funext i
  have hi := congrFun hc' i
  exact (IsFractionRing.injective x.A x.Fr)
    (((mul_eq_zero.mp hi).resolve_right (pow_ne_zero _ ht)).trans (map_zero _).symm)
end

