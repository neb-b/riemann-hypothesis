module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UnivDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0043

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.StableField
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.stable_field :
    ∀ {n : ℕ} {A G κ κ' : Type} [CommRing A] [Group G] [Field κ] [IsAlgClosed κ] [Field κ'] [IsAlgClosed κ'] (D : GDet n A G) (f : A →+* κ) (f' : A →+* κ'), RingHom.ker f = RingHom.ker f' → (∃ ρ : G →* Matrix (Fin n) (Fin n) κ, UpperTheory.V.U3.MatIrr ⊤ ρ ∧ D.map f = GDet.ofRep ρ) → ∃ ρ : G →* Matrix (Fin n) (Fin n) κ', UpperTheory.V.U3.MatIrr ⊤ ρ ∧ D.map f' = GDet.ofRep ρ := by
  intro n A G κ κ' _ _ _ _ _ _ D f f' hker ⟨ρ, hρ, hD⟩
  obtain ⟨ρ', hD'⟩ : ∃ ρ' : G →* Matrix (Fin n) (Fin n) κ', D.map f' = GDet.ofRep ρ' := by
    obtain ⟨r, -, hr⟩ := exists_semisimple_rep_of_detLaw_of_isAlgClosed (D.map f').toDet
    let ρ' := r.toMonoidHom.comp (MonoidAlgebra.of κ' G)
    have hrep : GDet.repAlg ρ' κ' = r := by
      apply MonoidAlgebra.algHom_ext
      · intro g
        simp [GDet.repAlg, ρ', MonoidAlgebra.lift_single]
      · ext
    refine ⟨ρ', Eq.symm ?_⟩
    suffices h : (GDet.ofRep ρ').toDet = (D.map f').toDet by
      rw [← GDet.ofDet_toDet (GDet.ofRep ρ'), h, GDet.ofDet_toDet]
    rw [← hr, ← hrep]
    refine Det.ext' fun S _ _ x => ?_
    change (GDet.repAlg ρ' S (ofT κ' G S x)).det = (Det.repS (GDet.repAlg ρ' κ') S x).det
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
  refine ⟨ρ', ?_, hD'⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    exact (UpperTheory.V.AlgebraTools.Det.matIrrIff ⊤ ρ').2 (Subsingleton.elim _ _)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have htrace (K : Type) [Field K] (φ : A →+* K) (τ : G →* Matrix (Fin n) (Fin n) K)
      (hτ : D.map φ = GDet.ofRep τ) (g : G) :
      (τ g).trace = φ (D.tr (MonoidAlgebra.single g 1)) := by
    have hmap : (D.map φ).chi (MonoidAlgebra.single g 1) =
        (D.chi (MonoidAlgebra.single g 1)).map φ := by
      let _ : Algebra A K[X] := ((algebraMap K K[X]).comp φ).toAlgebra
      let ψ : A[X] →ₐ[A] K[X] :=
        { Polynomial.mapRingHom φ with commutes' := fun _ => Polynomial.map_C φ }
      have hψ (x : A[X]) : ψ x = x.map φ := rfl
      have h := D.nat A[X] K[X] ψ (MonoidAlgebra.single 1 X - MonoidAlgebra.single g 1)
      simpa only [GDet.chi, GDet.map, map_sub, MonoidAlgebra.mapRingHom_single,
        AlgHom.coe_toRingHom, hψ, Polynomial.map_X, map_one] using h
    have hchi : (GDet.ofRep τ).chi (MonoidAlgebra.single g 1) = (τ g).charpoly := by
      simp only [GDet.chi, MonoidAlgebra.mapRingHom_single, map_one]
      change (GDet.repAlg τ K[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.single g 1)).det = _
      rw [map_sub, Matrix.charpoly]
      congr 1
      ext i j
      by_cases hij : i = j <;> simp [GDet.repAlg, hij]
    rw [hτ, hchi] at hmap
    rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin, hmap]
    simp [GDet.tr, GDet.lam]
  let H : Subgroup G := ⊤
  obtain ⟨U, -, hU⟩ := UpperTheory.V.AlgebraTools.Det.irrOpen (ι := Fin n)
    (fun g : H => D.tr (MonoidAlgebra.single (g : G) 1))
  let p : PrimeSpectrum A := ⟨RingHom.ker f, RingHom.ker_isPrime f⟩
  have hp : p ∈ U := (hU κ f (ρ.comp H.subtype) p rfl (fun g => htrace κ f ρ hD g)).2
    ((UpperTheory.V.AlgebraTools.Det.matIrrIff H ρ).1 hρ)
  exact (UpperTheory.V.AlgebraTools.Det.matIrrIff H ρ').2
    ((hU κ' f' (ρ'.comp H.subtype) p hker (fun g => htrace κ' f' ρ' hD' g)).1 hp)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UnivDetMf
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem lc_of_ker {G M : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
    (φ : G →* M) (h : IsOpen (φ.ker : Set G)) : IsLocallyConstant φ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker φ h

private theorem chi_ofRep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) =
      ((X : A[X]) • (1 : Matrix (Fin n) (Fin n) A[X]) - (ρ g).map (algebraMap A A[X])).det := by
  change (GDet.repAlg ρ A[X] _).det = _
  congr 1
  rw [map_sub, MonoidAlgebra.mapRingHom_single]
  simp [GDet.repAlg]

private theorem cont_ofChars {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (χ : Fin n → G →* Aˣ) (h : ∀ i, IsOpen ((χ i).ker : Set G)) (I : Ideal A) : (GDet.ofChars χ).IsCont I := by
  intro i N
  have h1 : IsLocallyConstant fun g j => χ j g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have := fun j => (lc_of_ker (χ j) (h j)).eventually_eq x
    exact (Filter.eventually_all.2 this).mono fun y hy => funext hy
  have h2 := h1.comp fun v : Fin n → Aˣ => Ideal.Quotient.mk (I ^ N) ((-1) ^ i *
    (((X : A[X]) • (1 : Matrix (Fin n) (Fin n) A[X]) -
      (Matrix.diagonal fun j => (v j : A)).map (algebraMap A A[X])).det).coeff (n - i))
  convert h2 using 1
  funext g
  simp [GDet.lam, GDet.ofChars, chi_ofRep, GDet.diagRep]

private theorem fin_field (l : ℕ) [Fact l.Prime] {n : ℕ} {k G : Type} [Field k] [Finite k] [CharP k l] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (χ : Fin n → G →* kˣ)
    (hP : PhiCond (Γ := G) l) (ho : ∀ i, IsOpen ((χ i).ker : Set G)) (hi : Function.Injective χ) :
    Module.Finite k ((GDet.ofChars χ).CHQuot ∅) := by
  have hinj : Function.Injective (residue k) := (residue k).injective
  haveI : Finite (ResidueField k) := Finite.of_surjective _ residue_surjective
  haveI : CharP (ResidueField k) l := charP_of_injective_ringHom hinj l
  haveI : IsAdicComplete (maximalIdeal k) k := by
    rw [maximalIdeal_eq_bot]
    infer_instance
  let u : kˣ →* (ResidueField k)ˣ := Units.map (residue k).toMonoidHom
  have hu : Function.Injective u := Units.map_injective hinj
  let χ' : Fin n → G →* (ResidueField k)ˣ := fun i => u.comp (χ i)
  have ho' : ∀ i, IsOpen ((χ' i).ker : Set G) := fun i => by
    have : (χ' i).ker = (χ i).ker := MonoidHom.ker_comp_of_injective _ _ hu
    rw [this]
    exact ho i
  have hi' : Function.Injective χ' := fun i j hij =>
    hi (MonoidHom.ext fun g => hu (DFunLike.congr_fun hij g))
  obtain ⟨h, hm⟩ := exists_multFree_of_phiCond_of_injective_chars l χ' hP ho' hi'
  have hmap : (GDet.ofChars χ).map (residue k) = GDet.ofChars χ' := by
    unfold GDet.ofChars
    rw [(d_gmap (GDet.ofRep (GDet.diagRep χ))).2.2.2]
    congr 1
    ext g a b
    by_cases hab : a = b
    · subst hab
      simp [GDet.diagRep, χ', u]
    · simp [GDet.diagRep, hab]
  exact (finE (GDet.ofChars χ) χ' (cont_ofChars χ ho _) hmap hm ∅).2.1

theorem UpperTheory.V.CA.univDet_mf :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (χ : Fin n → G →* (ResidueField O)ˣ), PhiCond (Γ := G) l → (∀ i, IsOpen ((χ i).ker : Set G)) → Function.Injective χ → ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (D : GDet n R G), IsUnivDet O (GDet.ofChars χ) D := by
  intro l _ O _ _ _ _ _ _ n G _ _ _ _ _ χ hP ho hi
  exact univDet l O (GDet.ofChars χ) hP (cont_ofChars χ ho _) (fin_field l χ hP ho hi)
end

