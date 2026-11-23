module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0007
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.PolyCM
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ClCmquot
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem UpperTheory.V.CA.cmquot_of_finite {P R : Type} [CommRing P] [IsLocalRing P] [CommRing R]
    [IsLocalRing R] (hP : IsCM P) (φ : P →+* R) (hf : φ.Finite) [IsLocalHom φ] : IsCMQuot R := by
  letI := φ.toAlgebra
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hf.finiteType
  let N : Ideal (MvPolynomial (Fin n) P) := Ideal.comap g.toRingHom (maximalIdeal R)
  haveI : N.IsMaximal := Ideal.comap_isMaximal_of_surjective g.toRingHom hg
  have hgC : g.toRingHom.comp MvPolynomial.C = φ := by
    refine RingHom.ext fun x => ?_
    show g (MvPolynomial.C x) = φ x
    rw [← MvPolynomial.algebraMap_eq, g.commutes]
    rfl
  have hC : Ideal.comap MvPolynomial.C N = maximalIdeal P := by
    have h := congrArg PrimeSpectrum.asIdeal (IsLocalRing.comap_closedPoint φ)
    show Ideal.comap MvPolynomial.C (Ideal.comap g.toRingHom (maximalIdeal R)) = maximalIdeal P
    rw [Ideal.comap_comap, hgC]
    exact h
  obtain ⟨hcm, -⟩ := isCM_localization_mvPolynomial hP n N hC
  have hu : ∀ y : N.primeCompl, IsUnit (g.toRingHom y) := fun y =>
    IsLocalRing.notMem_maximalIdeal.mp y.2
  refine ⟨Localization.AtPrime N, inferInstance, inferInstance, IsLocalization.lift hu, hcm, ?_⟩
  intro r
  obtain ⟨p, rfl⟩ := hg r
  exact ⟨algebraMap _ _ p, IsLocalization.lift_eq hu p⟩

theorem UpperTheory.V.CA.cl_cmquot :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R], IsCL O R → IsCMQuot R := by
  intro O _ _ _ _ R _ _ _ hR
  haveI := hR.noeth
  obtain ⟨n, a, ha⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian (maximalIdeal R))
  have hspan : Ideal.span (Set.range a) = maximalIdeal R := ha
  have hmem : ∀ s, a s ∈ maximalIdeal R := by
    intro s
    rw [← hspan]
    exact Ideal.subset_span ⟨s, rfl⟩
  have hrad : maximalIdeal R ≤
      (Ideal.span (Set.range a) ⊔ Ideal.map (algebraMap O R) (maximalIdeal O)).radical := by
    rw [hspan]
    exact le_sup_left.trans Ideal.le_radical
  obtain ⟨φ, -, hfin, hloc⟩ := cl_mvps O R hR (Fin n) a hmem hrad
  haveI := hloc
  exact cmquot_of_finite (cl_cm.1 O n).1 φ hfin
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinEGma
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem lift_surj {B E E' P : Type} [CommRing B] [Ring E] [Ring E'] [Ring P] [Algebra B E] [Algebra B E']
    [Algebra B P] (q : E →ₐ[B] E') (hq : Function.Surjective q) (ρ : E →ₐ[B] P) (h : ∀ x, q x = 0 → ρ x = 0) :
    ∃ π : E' →ₐ[B] P, ∀ x, π (q x) = ρ x := by
  have key : ∀ x y, q x = q y → ρ x = ρ y := fun x y hxy =>
    sub_eq_zero.1 (by rw [← map_sub]; exact h _ (by rw [map_sub, hxy, sub_self]))
  choose s hs using hq
  have hq' : ∀ x, ρ (s (q x)) = ρ x := fun x => key _ _ (hs _)
  refine ⟨⟨⟨⟨⟨fun y => ρ (s y), ?_⟩, fun a b => ?_⟩, ?_, fun a b => ?_⟩, fun r => ?_⟩, hq'⟩
  · rw [← map_one q, hq', map_one]
  · change ρ (s (a * b)) = ρ (s a) * ρ (s b)
    rw [← map_mul]
    exact key _ _ (by rw [map_mul, hs, hs, hs])
  · change ρ (s 0) = 0
    rw [← map_zero q, hq', map_zero]
  · change ρ (s (a + b)) = ρ (s a) + ρ (s b)
    rw [← map_add (f := _)]
    exact key _ _ (by rw [map_add (f := _), hs, hs, hs])
  · change ρ (s (algebraMap B E' r)) = _
    rw [← q.commutes, hq', ρ.commutes]

theorem UpperTheory.V.CA.finE_gma :
    ∀ {n h : ℕ} {B G : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [Finite (ResidueField B)] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (D : GDet n B G) (χ : Fin n → G →* (ResidueField B)ˣ), D.IsCont (maximalIdeal B) → D.map (residue B) = GDet.ofChars χ → MultFree χ h → ∀ Z : Set (MonoidAlgebra B G), (∀ z ∈ Z, D.Kills z) → ∃ (DE : Det n B (D.CHQuot Z)) (π : D.CHQuot Z →ₐ[B] (Fin n → ResidueField B)) (e : Fin n → D.CHQuot Z), DE.pull (D.toQuot Z) = D.toDet ∧ IsGMA DE e ∧ Function.Surjective π ∧ (∀ g i, π (D.toQuot Z (MonoidAlgebra.single g 1)) i = χ i g) ∧ (∀ x, π x = 0 ↔ x ∈ Ring.jacobson (D.CHQuot Z)) ∧ (∀ i, π (e i) = Pi.single i 1) ∧ ∀ x, (DE.chi x).map (residue B) = ∏ i, (X - C (π x i)) := by
  intro n h B G _ _ _ _ _ _ _ _ _ _ D χ hc hred hm Z hZ
  obtain ⟨DE, hCH, hDE⟩ := d_quotDet D hc Z hZ
  obtain ⟨π0, hs0, hg0, -, hchi0⟩ := f_chars χ hm.inj
  let ρ : MonoidAlgebra B G →ₐ[B] (Fin n → ResidueField B) :=
    (π0.restrictScalars B).comp (MonoidAlgebra.mapAlgHom G (Algebra.ofId B (ResidueField B)))
  have hρ : ∀ x, ρ x = π0 (MonoidAlgebra.mapRingHom G (residue B) x) := fun x => rfl
  have hchi : ∀ x, (DE.chi (D.toQuot Z x)).map (residue B) = ∏ i, (X - C (ρ x i)) := fun x => by
    rw [← (d_pull DE (D.toQuot Z)).1, hDE, (d_toDet D x).1, ← ((d_gmap D).2.2.1 (residue B) x).1, hred, hchi0, hρ]
  have hsurj : Function.Surjective (D.toQuot Z) := fun q => Quotient.exists_rep q
  have hker : ∀ x, D.toQuot Z x = 0 → ρ x = 0 := fun x hx => by
    have h1 := hchi x
    rw [hx, ← map_zero (D.toQuot Z), hchi 0, map_zero] at h1
    funext i
    have h2 := congrArg (eval (ρ x i)) h1
    rw [eval_prod, eval_prod, Finset.prod_eq_zero (f := fun j => eval (ρ x i) (X - C (ρ x j)))
      (Finset.mem_univ i) (by simp)] at h2
    obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.1 h2
    simpa using hj
  obtain ⟨π, hπ⟩ := lift_surj (D.toQuot Z) hsurj ρ hker
  have hmap : ∀ y : MonoidAlgebra (ResidueField B) G, ∃ x, MonoidAlgebra.mapRingHom G (residue B) x = y := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => exact ⟨0, map_zero _⟩
    | add a b ha hb =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      exact ⟨a' + b', map_add _ _ _⟩
    | single g r =>
      obtain ⟨c, rfl⟩ := residue_surjective r
      exact ⟨MonoidAlgebra.single g c, MonoidAlgebra.mapRingHom_single _ _ _⟩
  have hπs : Function.Surjective π := fun v => by
    obtain ⟨y, rfl⟩ := hs0 v
    obtain ⟨x, rfl⟩ := hmap y
    exact ⟨D.toQuot Z x, by rw [hπ, hρ]⟩
  have hchiE : ∀ x, (DE.chi x).map (residue B) = ∏ i, (X - C (π x i)) := fun x => by
    obtain ⟨y, rfl⟩ := hsurj x
    rw [hπ, hchi]
  haveI : IsLocalHom (algebraMap B (ResidueField B)) := inferInstanceAs (IsLocalHom (residue B))
  obtain ⟨hj, e, he, hπe⟩ := f_gma DE π hCH hπs hchiE
  refine ⟨DE, π, e, hDE, he, hπs, fun g i => ?_, hj, hπe, hchiE⟩
  rw [hπ, hρ, MonoidAlgebra.mapRingHom_single, map_one, hg0]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GroupDetExistsSemisimpleRepresentation
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.groupDet_exists_semisimple_representation :
    ∀ {n : ℕ} {k G : Type} [Field k] [IsAlgClosed k] [Group G] (D : GDet n k G), ∃ ρ : G →* Matrix (Fin n) (Fin n) k, IsSemisimpleRing (GDet.repAlg ρ k).range ∧ GDet.ofRep ρ = D ∧ ∀ y, D.Kills y ↔ GDet.repAlg ρ k y = 0 := by
  intro n k G _ _ _ D
  obtain ⟨r, hss, hD⟩ := exists_semisimple_rep_of_detLaw_of_isAlgClosed D.toDet
  let ρ : G →* Matrix (Fin n) (Fin n) k := (r : MonoidAlgebra k G →* Matrix (Fin n) (Fin n) k).comp
    (MonoidAlgebra.of k G)
  have hr : GDet.repAlg ρ k = r := by
    apply MonoidAlgebra.algHom_ext
    · intro g
      simp [GDet.repAlg, ρ, MonoidAlgebra.lift_single]
    · ext
  refine ⟨ρ, hr ▸ hss, ?_, fun y => ?_⟩
  · have hrep : (GDet.ofRep ρ).toDet = Det.ofRep (Fintype.card_fin n) (GDet.repAlg ρ k) := by
      refine Det.ext' fun S _ _ x => ?_
      change (GDet.repAlg ρ S (ofT k G S x)).det = (Det.repS (GDet.repAlg ρ k) S x).det
      congr 1
      induction x with
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | tmul s y =>
        rw [ofT_tmul, Det.repS_tmul, map_smul]
        congr 1
        induction y using MonoidAlgebra.induction_linear with
        | zero => ext i j; simp
        | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]; ext i j; simp
        | single g a => ext i j; simp [GDet.repAlg]
    rw [← GDet.ofDet_toDet (GDet.ofRep ρ), hrep, hr, hD, GDet.ofDet_toDet]
  · have hval (S : Type) [CommRing S] [Algebra k S] (h : S ⊗[k] MonoidAlgebra k G) :
        D.toDet.D S (1 + h * (1 ⊗ₜ y)) =
          D.D S (1 + ofT k G S h * MonoidAlgebra.mapRingHom G (algebraMap k S) y) := by
      change D.D S (ofT k G S (1 + h * (1 ⊗ₜ y))) = _
      rw [map_add (f := _), map_one, map_mul, ofT_tmul, one_smul]
    have hkills : D.toDet.Kills y ↔ D.Kills y := by
      constructor
      · intro hk S _ _ h
        have hh := hk S (toT k G S h)
        rwa [hval, ofT_toT] at hh
      · intro hk S _ _ h
        rw [hval]
        exact hk S _
    rw [← hkills, ← (d_ker D.toDet y).1, ← hD, d_ker_ss _ r hss, hr]
end

