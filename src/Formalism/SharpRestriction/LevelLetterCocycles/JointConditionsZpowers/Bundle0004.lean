module

public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0003
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CoefficientCompatibilityOf
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

open NumberField IsDedekindDomain

theorem continuous_family_of (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : GoodR D.nd i r) : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r := by
  intro x
  exact (hr x).1

theorem semisimple_family_of (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : GoodR D.nd i r) : Formalism.MainNotions.TruncatedSeriesCountingIdentities.admSS (D := D) i r := by
  intro x W hW
  obtain ⟨W', hW', hc⟩ := (hr x).2.1 W hW
  exact ⟨W', hW', hc⟩

theorem coefficient_compatibility_of (D : D7) (i : D.nd.Loc)
    (hdeg : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), Br.DegW D.nbr i w hw) :
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility (D := D) i := by
  intro w hw
  exact ⟨(D.nbr i w hw).eO_alg, ⟨(D.nbr i w hw).eO_cont, (D.nbr i w hw).eO_symm_cont⟩, hdeg w hw⟩

theorem isOpen_ker_redRep (D : D7) (a : D.nd.Loc) {n : ℕ} (ρ : G D.host.E D.nd.Om →* GL (Fin n) (D.nd.O a))
    (h : Continuous (fun g => ((ρ g : GL (Fin n) (D.nd.O a)) : Matrix (Fin n) (Fin n) (D.nd.O a)))) :
    IsOpen ((redRep D.nd a ρ).ker : Set (G D.host.E D.nd.Om)) := by
  have hm : IsOpen ((IsLocalRing.maximalIdeal (D.nd.O a) : Ideal (D.nd.O a)) : Set (D.nd.O a)) := by
    simpa using (isAdic_iff.mp (D.nd.O_adic a)).1 1
  have hset : ((redRep D.nd a ρ).ker : Set (G D.host.E D.nd.Om)) =
      ⋂ i, ⋂ j, (fun g => ((ρ g : GL (Fin n) (D.nd.O a)) : Matrix (Fin n) (Fin n) (D.nd.O a)) i j -
        (1 : Matrix (Fin n) (Fin n) (D.nd.O a)) i j) ⁻¹'
        ((IsLocalRing.maximalIdeal (D.nd.O a) : Ideal (D.nd.O a)) : Set (D.nd.O a)) := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_preimage]
    rw [Units.ext_iff, ← Matrix.ext_iff]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    have h1 : ((1 : GL (Fin n) (IsLocalRing.ResidueField (D.nd.O a))) :
        Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField (D.nd.O a))) i j =
        IsLocalRing.residue (D.nd.O a) ((1 : Matrix (Fin n) (Fin n) (D.nd.O a)) i j) := by
      rw [Units.val_one, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [h1]
    exact Ideal.Quotient.eq
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact hm.preimage ((h.matrix_elem i j).sub continuous_const)

theorem charpoly_of_decomp (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hdec : Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π) (g : GE D.nd) :
    (rO D.nd i r π g).charpoly = (rhoO D.nd i ρ π g).charpoly *
      ∏ c ∈ Finset.Icc 1 D.R.t, (X - C ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i)) := by
  obtain ⟨e, he⟩ := hdec
  apply Polynomial.map_injective (toK D.nd i) (IsFractionRing.injective (D.nd.O i) (KK D.nd i))
  rw [Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, ← Matrix.charpoly_map]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  show (mapM (toK D.nd i) (rO D.nd i r π) g).charpoly = (mapM (toK D.nd i) (rhoO D.nd i ρ π) g).charpoly *
    ∏ c ∈ Finset.Icc 1 D.R.t, (X - C (toK D.nd i ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i)))

  have hmat : ∀ {m : ℕ} (M : Matrix (Fin m) (Fin m) (KK D.nd i)), (Matrix.toLin' M).charpoly = M.charpoly := by
    intro m M
    rw [← LinearMap.charpoly_toMatrix (Matrix.toLin' M) (Pi.basisFun (KK D.nd i) (Fin m)),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

  have hconj : e.conj (Matrix.toLin' (mapM (toK D.nd i) (rO D.nd i r π) g)) =
      (Matrix.toLin' (mapM (toK D.nd i) (rhoO D.nd i ρ π) g)).prodMap
        (Matrix.toLin' (Matrix.diagonal fun c : Fin D.R.t =>
          toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i))) := by
    apply LinearMap.ext
    intro p
    obtain ⟨u, rfl⟩ := e.surjective p
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      Matrix.toLin'_apply, LinearMap.prodMap_apply]
    rw [he g u]
    refine Prod.ext rfl (funext fun c => ?_)
    simp [Matrix.mulVec_diagonal]
  have hdiag : (Matrix.diagonal fun c : Fin D.R.t =>
      toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i)).charpoly =
      ∏ c : Fin D.R.t, (X - C (toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i))) := by
    have hch : Matrix.charmatrix (Matrix.diagonal fun c : Fin D.R.t =>
        toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i)) =
        Matrix.diagonal fun c : Fin D.R.t =>
          (X - C (toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i))) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp [Matrix.charmatrix_apply]
      · simp [Matrix.charmatrix_apply, hab, Matrix.diagonal_apply_ne _ hab]
    rw [Matrix.charpoly, hch, Matrix.det_diagonal]

  have hidx : ∏ c : Fin D.R.t, (X - C (toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i))) =
      ∏ c ∈ Finset.Icc 1 D.R.t, (X - C (toK D.nd i ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i))) := by
    rw [Fin.prod_univ_eq_prod_range (fun c => X - C (toK D.nd i ((chiU D.nd i (c + 1) g : (D.nd.O i)ˣ) : D.nd.O i))),
      Finset.range_eq_Ico,
      Finset.prod_Ico_add' (fun c => X - C (toK D.nd i ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i))) 0 D.R.t 1]
    congr 1
  rw [← hmat, ← LinearEquiv.charpoly_conj e, hconj, LinearMap.charpoly_prodMap, hmat, hmat, hdiag, hidx]

def AbsIrreducibleDistinct (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) : Prop :=
  ∀ x, AbsIrrDistinct (repK D.nd i r x)

end Formalism.MainNotions.N
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfCrystallineLift
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

open NumberField IsDedekindDomain

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V'] {ρ' : Representation LL G V'}
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'}

theorem LiftF_mono (F : LatHom L L') {e e' : ℕ} (he : e ≤ e') (h : F.LiftF PD e) : F.LiftF PD e' := by
  intro c hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add, mul_comm, mul_smul]
  exact (F.ImF PD).smul_mem _ (h c hc)

end Gen

section Fields

variable {l : ℕ} [Fact l.Prime]

theorem Ks_mono (K : FinExt l) {s s' : ℕ} (h : s ≤ s') : Ks K s ≤ Ks K s' := by
  unfold Formalism.BasicNotions.Loc.Ks
  refine sup_le_sup_left ?_ _
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  apply IntermediateField.subset_adjoin
  simp only [Set.mem_setOf_eq] at hx ⊢
  obtain ⟨c, hc⟩ := pow_dvd_pow l h
  rw [hc, pow_mul, hx, one_pow]

theorem caseA_of_unram (P : LocPrime l) (H : LocHW l P) {K : FinExt l} {LL : FinExt l} (h : Good K 1 LL)
    (hK : K.1 ≤ MaximalUnramifiedExtension l) (hl : l ≠ 2) : Formalism.MainNotions.LiftingTheory.CaseA (H.W K 1 LL h) := by
  refine ⟨⟨RingHom.injective (algebraMap ↥(K0 K) ↥K.1), fun y =>
    ⟨⟨(y : Om l), IntermediateField.mem_inf.mpr ⟨y.2, hK y.2⟩⟩, by ext; rfl⟩⟩, H.W_s K 1 LL h, ?_⟩
  rw [P.PD_p K]
  exact hl

end Fields

theorem Hmax_const_le (n M h : ℕ) : Formalism.MainNotions.LiftingTheory.Hmax n (fun _ => M) (fun _ => h) ≤ M + h := by
  unfold Formalism.MainNotions.LiftingTheory.Hmax
  exact Finset.sup_le fun _ _ => le_rfl

end Formalism.MainNotions.N
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

open NumberField IsDedekindDomain

def GlobalDatumResidualRepCondition (D : D7) : Prop :=
  ∀ (a : D.nd.Loc) (x : D.nd.X a), x ∈ ZgoodN D.nd D.naut a → ∀ Sig, HasParamX D.nd D.naut a x Sig →
    goodSig D.nd D.naut Sig → ∃ (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O a))
      (ξ : G D.host.E D.nd.Om →* (D.nd.O a)ˣ), IsRepOfSig D.nd D.naut a Sig ρ ∧
      (∀ k, D.nd.l a ≠ D.host.g k → ∀ v ∈ placesOver D.host.E (D.host.g k),
        ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), ξ σ = 1) ∧
      IsRhoOf D.nd a x (Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ)

theorem mapRep_twGL_coe {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin n) A) (ξ : Γ →* Aˣ) (g : Γ) :
    ((mapRep f (Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ) g : GL _ _) : Matrix (Fin n) (Fin n) B) =
      f ((ξ g : Aˣ) : A) • ((mapRep f ρ g : GL _ _) : Matrix (Fin n) (Fin n) B) := by
  ext i j
  simp [mapRep, Formalism.MainNotions.SumRepresentations.At.twGL]
  rw [← Matrix.map_mul, ← Algebra.smul_def]
  simp

theorem irredOn_twGL {Γ : Type} [Group Γ] {A : Type} [CommRing A] {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}
    (f : A →+* Formalism.CyclotomicNorms.Fbar ℓ) (ρ : Γ →* GL (Fin n) A) (ξ : Γ →* Aˣ)
    (h : Formalism.CyclotomicNorms.IrredOn (mapRep f ρ) ⊤) : Formalism.CyclotomicNorms.IrredOn (mapRep f (Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ)) ⊤ := by
  intro W hW
  refine h W ?_
  intro g _ x hx
  have h1 := hW g (Subgroup.mem_top g) x hx
  rw [mapRep_twGL_coe] at h1

  have hsm : ∀ (c : Formalism.CyclotomicNorms.Fbar ℓ) (M : Matrix (Fin n) (Fin n) (Formalism.CyclotomicNorms.Fbar ℓ)) (v : Fin n → Formalism.CyclotomicNorms.Fbar ℓ),
      (c • M).mulVec v = c • M.mulVec v := by
    intro c M v
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [hsm] at h1
  obtain ⟨u, hu⟩ := (Units.isUnit (ξ g)).map f
  have h2 := W.smul_mem ((u⁻¹ : (Formalism.CyclotomicNorms.Fbar ℓ)ˣ) : Formalism.CyclotomicNorms.Fbar ℓ) h1
  rwa [← hu, smul_smul, Units.inv_mul, one_smul] at h2

def GlobalDatumDepthZeroCondition (D : D7) : Prop :=
  ∀ (a : D.nd.Loc) (x : D.nd.X a), x ∈ ZgoodN D.nd D.naut a → ∀ Sig, HasParamX D.nd D.naut a x Sig →
    ∀ (k : Fin 2) (v : D.nd.PlG k),
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree =
        D.naut.lpDim (isoLoc D.nd D.naut Sig (D.naut.plGw k v))

theorem placesOver_finite_joint_conditions_zpowers (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have hx : ((p : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hI : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq]
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

private theorem charpoly_eq_of_frob_on_split_places (D : D7) {k : Type} [Field k] {n : ℕ}
    (hC : ∀ Sg : Set (PlE D.host), Sg.Finite →
      closure {σ : G D.host.E D.nd.Om | ∃ w ∉ Sg, IsSplitPl D.host w ∧ ∃ B : ValuationSubring D.nd.Om,
        IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ} = Set.univ)
    (rb rb' : G D.host.E D.nd.Om →* GL (Fin n) k)
    (ho : IsOpen (rb.ker : Set (G D.host.E D.nd.Om))) (ho' : IsOpen (rb'.ker : Set (G D.host.E D.nd.Om)))
    (Sg : Set (PlE D.host)) (hSg : Sg.Finite)
    (hfr : ∀ w ∉ Sg, IsSplitPl D.host w → ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
      ((rb σ : GL _ _) : Matrix (Fin n) (Fin n) k).charpoly = ((rb' σ : GL _ _) : Matrix (Fin n) (Fin n) k).charpoly)
    (g : G D.host.E D.nd.Om) :
    ((rb g : GL _ _) : Matrix (Fin n) (Fin n) k).charpoly = ((rb' g : GL _ _) : Matrix (Fin n) (Fin n) k).charpoly := by

  have hcl : IsClosed {g' : G D.host.E D.nd.Om |
      ((rb g' : GL _ _) : Matrix (Fin n) (Fin n) k).charpoly = ((rb' g' : GL _ _) : Matrix (Fin n) (Fin n) k).charpoly} := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro g0 hg0
    refine ⟨(fun k => g0 * k) '' ((rb.ker ⊓ rb'.ker : Subgroup (G D.host.E D.nd.Om)) : Set (G D.host.E D.nd.Om)),
      ?_, ?_, ⟨1, Subgroup.one_mem _, mul_one g0⟩⟩
    · rintro _ ⟨k, hk, rfl⟩ hgk
      obtain ⟨hk1, hk2⟩ := Subgroup.mem_inf.mp hk
      rw [MonoidHom.mem_ker] at hk1 hk2
      apply hg0
      simpa only [Set.mem_setOf_eq, map_mul, hk1, hk2, mul_one] using hgk
    · refine isOpenMap_mul_left g0 _ ?_
      rw [Subgroup.coe_inf]
      exact ho.inter ho'
  have hg : g ∈ closure {σ : G D.host.E D.nd.Om | ∃ w ∉ Sg, IsSplitPl D.host w ∧ ∃ B : ValuationSubring D.nd.Om,
      IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ} := by
    rw [hC _ hSg]
    exact Set.mem_univ g
  refine closure_minimal ?_ hcl hg
  rintro σ ⟨w, hw, hsp, B, hB, hF⟩
  exact hfr w hw hsp B σ hB hF

theorem residual_irreducible_of_theorem (D : D7) (h3p : Formalism.MainNotions.ArithmeticCylinders.TheoremThreePrime D) (hAN : Formalism.MainNotions.SumRepresentations.adm5 D)
    (hBN : LitBNIrr (G D.host.E D.nd.Om)) (hrho : GlobalDatumResidualRepCondition D) (hdz : GlobalDatumDepthZeroCondition D) :
    ResidualIrreducibleRankR D := by
  intro a hHG rb hrb
  obtain ⟨x, hx⟩ := hHG
  have hx' := hx
  obtain ⟨-, Sig, hSig, hgood⟩ := hx'
  obtain ⟨ρ, ξ, hrep, hξ, hrx⟩ := hrho a x hx Sig hSig hgood
  have hBB : Disjoint (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0)) (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1)) := D.ntypes.BB_disj
  have H3 := (h3p hBB a Sig ⟨x, hSig⟩ (hdz a x hx Sig hSig) hgood).2 ρ hrep

  have hm : IsOpen ((IsLocalRing.maximalIdeal (D.nd.O a) : Ideal (D.nd.O a)) : Set (D.nd.O a)) := by
    simpa using (isAdic_iff.mp (D.nd.O_adic a)).1 1

  have hker : IsOpen ((mapRep (IsLocalRing.residue (D.nd.O a)) (Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ)).ker :
      Set (G D.host.E D.nd.Om)) := by
    have hset : ((mapRep (IsLocalRing.residue (D.nd.O a)) (Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ)).ker : Set (G D.host.E D.nd.Om)) =
        ⋂ i, ⋂ j, (fun g => ((Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ g : GL (Fin D.R.r) (D.nd.O a)) :
          Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) i j - (1 : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) i j) ⁻¹'
          ((IsLocalRing.maximalIdeal (D.nd.O a) : Ideal (D.nd.O a)) : Set (D.nd.O a)) := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_preimage]
      rw [Units.ext_iff, ← Matrix.ext_iff]
      refine forall_congr' fun i => forall_congr' fun j => ?_
      have h1 : ((1 : GL (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O a))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O a))) i j =
          IsLocalRing.residue (D.nd.O a) ((1 : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O a)) i j) := by
        rw [Units.val_one, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [h1]
      exact Ideal.Quotient.eq
    rw [hset]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact hm.preimage ((hrx.1.matrix_elem i j).sub continuous_const)

  have hcp : ∀ g, ((rb g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O a))).charpoly =
      ((mapRep (IsLocalRing.residue (D.nd.O a)) (Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ) g : GL _ _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O a))).charpoly := by
    refine charpoly_eq_of_frob_on_split_places D hAN.2.2.1 _ _ hrb.1 hker
      (placesOver D.host.E (D.nd.l a) ∪ ↑(D.nd.S a) ∪ ↑(D.nd.Q a))
      (((placesOver_finite_joint_conditions_zpowers D.host.E (D.nd.l a) (D.nd.lPrime a).out.ne_zero).union
        (D.nd.S a).finite_toSet).union (D.nd.Q a).finite_toSet) ?_
    intro w hw hsp B σ hB hF
    simp only [Set.mem_union, not_or, Finset.mem_coe] at hw
    have hso : SplitOut D.nd a w := ⟨hsp, hw.1.1, hw.1.2, hw.2⟩
    have e1 := hrb.2 x w hso B σ hB hF
    have e2 := congrArg (Polynomial.map (IsLocalRing.residue (D.nd.O a))) (hrx.2.2 w hso B σ hB hF)
    rw [Polynomial.map_mul, ← Matrix.charpoly_map, Polynomial.map_prod] at e2
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at e2
    exact mul_right_cancel₀ (Polynomial.Monic.ne_zero
      (Polynomial.monic_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C _))) (e1.trans e2.symm)
  have hcomp : mapRep (D.naut.kFbar a) (mapRep (IsLocalRing.residue (D.nd.O a)) (Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ)) =
      mapRep ((D.naut.kFbar a).comp (IsLocalRing.residue (D.nd.O a))) (Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ) := by
    ext g i j
    simp [mapRep]
  have hirr0 : Formalism.CyclotomicNorms.IrredOn (mapRep (D.naut.kFbar a)
      (mapRep (IsLocalRing.residue (D.nd.O a)) (Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ))) ⊤ := by
    rw [hcomp]
    exact irredOn_twGL _ ρ ξ H3.1
  refine ⟨hBN (D.nd.l a) D.R.r _ _ ?_ hirr0, ?_⟩
  · intro g
    have e := congrArg (Polynomial.map (D.naut.kFbar a)) (hcp g)
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_map] at e
    exact e
  · intro k hk v hv

    have hvS : v ∈ D.nd.S a := by
      rw [D.nd.S_def]
      refine ⟨?_, ?_⟩
      · fin_cases k
        · exact Or.inl hv
        · exact Or.inr (Or.inl hv)
      · intro hvl
        have hcop : IsCoprime ((D.host.g k : ℤ)) ((D.nd.l a : ℤ)) :=
          Nat.isCoprime_iff_coprime.mpr
            ((Nat.coprime_primes (D.host.g_prime k) (D.nd.lPrime a).out).mpr (Ne.symm hk))
        obtain ⟨u, u', huu⟩ := hcop.map (Int.castRingHom (𝓞 D.host.E))
        simp only [eq_intCast, Int.cast_natCast] at huu
        have h1 : (1 : 𝓞 D.host.E) ∈ v.asIdeal := by
          rw [← huu]
          exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left u hv) (v.asIdeal.mul_mem_left u' hvl)
        exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    have hT := D.nd.restN_tameGenerator_generates a v (Or.inl hvS)
    have hξ1 : ξ (D.nd.gam0 a v) = 1 := hξ k hk v hv _ hT.1
    have hnr := H3.2.2 k hk v hv hT.2
    intro hroot
    apply hnr
    rw [hcp] at hroot
    have hr0 : ((mapRep (IsLocalRing.residue (D.nd.O a)) (Formalism.MainNotions.SumRepresentations.At.twGL ρ ξ) (D.nd.gam0 a v) : GL _ _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O a))) =
        ((mapRep (IsLocalRing.residue (D.nd.O a)) ρ (D.nd.gam0 a v) : GL _ _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O a))) := by
      rw [mapRep_twGL_coe, hξ1]
      simp
    rw [hr0] at hroot
    have h2 := hroot.map (f := D.naut.kFbar a)
    rw [← Matrix.charpoly_map] at h2
    exact h2

end Formalism.MainNotions.N
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.WachRestrictionOfLiftingPackage
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem lifting_local_of_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ) (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.LiftingTheory.ConclusionL D HW F := h.1

theorem wach_of_lifting_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ) (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.LiftingTheory.ConclusionW D HW F := h.2.1

theorem lift_of_lifting_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ) (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.LiftingTheory.LiftTheoremAllCases D HW F CA CB CK := h.2.2.2.2.2.2.2

end Formalism.MainNotions.N
end
end

