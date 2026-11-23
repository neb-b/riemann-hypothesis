module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0030
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisedGlobalCocyclesInLocalSpan
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.LocCoc

theorem factor {O K Γ X W : Type} [CommRing O] [IsNoetherianRing O] [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) [Group Γ] [Fintype X] [AddCommGroup W] [Module O W] {n : ℕ}
    (P : X → Prop) (A : X → (Γ →* Matrix (Fin n) (Fin n) O)) (E : X → Matrix (Fin n) (Fin n) O)
    (y : Γ → X → Matrix (Fin n) (Fin n) O) (hy : ∀ γ x, y γ x = (A x γ - 1) * E x)
    (φ : (X → Matrix (Fin n) (Fin n) O) →ₗ[O] W) (ρ : Γ → W →ₗ[O] W)
    (h1 : ∀ γ δ, φ ((fun x => A x γ) * y δ) = ρ γ (φ (y δ)))
    (h0 : ∀ z ∈ Submodule.span O (Set.range y), (∀ x, P x → z x = 0) → φ z = 0) :
    ∃ (a : ℕ) (q : Fin a → X) (_ : ∀ j, P (q j)) (E' : Fin a → Fin n → K)
      (Y : Submodule O (Fin a → Fin n → K)) (_ : Y.FG)
      (hst : ∀ γ : Γ, ∀ z ∈ Y, (fun j => (mapM (algebraMap O K) (A (q j)) γ).mulVec (z j)) ∈ Y)
      (hE : ∀ γ : Γ, (fun j => (mapM (algebraMap O K) (A (q j)) γ).mulVec (E' j) - E' j) ∈ Y)
      (φ' : ↥Y →ₗ[O] W),
      (∀ (γ : Γ) (z : ↥Y), φ' ⟨_, hst γ z.1 z.2⟩ = ρ γ (φ' z)) ∧ ∀ γ, φ' ⟨_, hE γ⟩ = φ (y γ) := by
  classical
  let e := (Fintype.equivFin ({x // P x} × Fin n)).symm
  let L : (X → Matrix (Fin n) (Fin n) O) →ₗ[O] (Fin (Fintype.card ({x // P x} × Fin n)) → Fin n → K) :=
    { toFun := fun z j s => algebraMap O K (z (e j).1.1 s (e j).2)
      map_add' := fun a b => by funext j s; simp
      map_smul' := fun c a => by funext j s; simp [Algebra.smul_def] }
  have key : ∀ (γ : Γ) (z : X → Matrix (Fin n) (Fin n) O),
      (fun j => (mapM (algebraMap O K) (A (e j).1.1) γ).mulVec (L z j)) = L ((fun x => A x γ) * z) := by
    intro γ z
    funext j s
    show ∑ t, algebraMap O K (A (e j).1.1 γ s t) * algebraMap O K (z (e j).1.1 t (e j).2) =
      algebraMap O K (∑ t, A (e j).1.1 γ s t * z (e j).1.1 t (e j).2)
    simp
  let Y0 := Submodule.span O (Set.range y)
  have hmul : ∀ γ δ, (fun x => A x γ) * y δ = y (γ * δ) - y γ := by
    intro γ δ
    funext x
    simp only [Pi.mul_apply, Pi.sub_apply, hy, map_mul]
    noncomm_ring
  have hst0 : ∀ γ, ∀ z ∈ Y0, (fun x => A x γ) * z ∈ Y0 ∧ φ ((fun x => A x γ) * z) = ρ γ (φ z) := by
    intro γ z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨δ, rfl⟩ := hz
      refine ⟨?_, h1 γ δ⟩
      rw [hmul]
      exact Y0.sub_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
    | zero => simp
    | add a b _ _ ha hb =>
      rw [mul_add, map_add (f := _), map_add (f := _), map_add (f := _), ha.2, hb.2]
      exact ⟨Y0.add_mem ha.1 hb.1, rfl⟩
    | smul c a _ ha =>
      rw [mul_smul_comm, map_smul, map_smul, map_smul, ha.2]
      exact ⟨Y0.smul_mem c ha.1, rfl⟩
  have hLE : ∀ γ, (fun j => (mapM (algebraMap O K) (A (e j).1.1) γ).mulVec (L E j) - L E j) = L (y γ) := by
    intro γ
    have : y γ = (fun x => A x γ) * E - E := by
      funext x
      simp [hy, sub_mul]
    rw [this, map_sub, ← key]
    rfl
  let L0 := L.domRestrict Y0
  have hker : LinearMap.ker L0 ≤ LinearMap.ker (φ.domRestrict Y0) := by
    intro z hz
    refine h0 z.1 z.2 fun x hx => ?_
    ext s t
    apply hinj
    have := congrFun (congrFun (LinearMap.mem_ker.mp hz) (e.symm (⟨x, hx⟩, t))) s
    simpa [L0, L] using this
  let φ' : ↥(LinearMap.range L0) →ₗ[O] W :=
    ((LinearMap.ker L0).liftQ (φ.domRestrict Y0) hker) ∘ₗ (L0.quotKerEquivRange.symm : _ →ₗ[O] _)
  have hφ' : ∀ (z : Y0) (h : L z.1 ∈ LinearMap.range L0), φ' ⟨L z.1, h⟩ = φ z.1 := by
    intro z h
    have : L0.quotKerEquivRange.symm ⟨L z.1, h⟩ = (LinearMap.ker L0).mkQ z :=
      L0.quotKerEquivRange_symm_apply_image z h
    simp only [φ', LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  refine ⟨_, fun j => (e j).1.1, fun j => (e j).1.2, L E, LinearMap.range L0, ?_, ?_, ?_, φ', ?_, ?_⟩
  · rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  · rintro γ _ ⟨z, rfl⟩
    exact ⟨⟨_, (hst0 γ z.1 z.2).1⟩, (key γ z.1).symm⟩
  · intro γ
    exact ⟨⟨y γ, Submodule.subset_span ⟨_, rfl⟩⟩, (hLE γ).symm⟩
  · rintro γ ⟨_, z, rfl⟩
    have h2 := hφ' ⟨_, (hst0 γ z.1 z.2).1⟩ ⟨⟨_, (hst0 γ z.1 z.2).1⟩, rfl⟩
    have h3 := hφ' z ⟨z, rfl⟩
    refine Eq.trans (Eq.trans (congrArg φ' (Subtype.ext ?_)) h2) ?_
    · exact key γ z.1
    rw [(hst0 γ z.1 z.2).2, ← h3]
    rfl
  · intro γ
    have h2 := hφ' ⟨y γ, Submodule.subset_span ⟨_, rfl⟩⟩ ⟨⟨y γ, Submodule.subset_span ⟨_, rfl⟩⟩, rfl⟩
    exact Eq.trans (congrArg φ' (Subtype.ext (hLE γ))) h2

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (S : IdempotentChoiceData D.nd i)

theorem inR'_tw (γ : GE D.nd) : InR' D.nd r S fun x' => rTwO D.nd i r (S.p x') γ := by
  refine ⟨1, fun _ => algebraMap (D.nd.O i) _ (((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i), fun _ => γ,
    fun _ => S.T'.algebraMap_mem _, ?_⟩
  funext x'
  simp [rTwO, twistM]

theorem inR'_one : InR' D.nd r S 1 := by
  refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, ?_⟩
  funext x'
  simp

theorem inY_yg (γ : GE D.nd) : InY D.nd r S (yg D.nd r S γ) :=
  ⟨1, fun _ => 1, fun _ => γ, fun _ => inR'_one i r S, by simp⟩

theorem inY_of_span (z : S.X' → MatN D.nd i)
    (hz : z ∈ Submodule.span (D.nd.O i) (Set.range (yg D.nd r S))) : InY D.nd r S z := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨δ, rfl⟩ := hz
    exact inY_yg i r S δ
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, a, γ, ha, rfl⟩ := ha
    obtain ⟨m', a', γ', ha', rfl⟩ := hb
    refine ⟨m + m', Fin.append a a', Fin.append γ γ', fun k => ?_, ?_⟩
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
      · simpa using ha k
      · simpa using ha' k
    · rw [Fin.sum_univ_add]
      simp
  | smul c a _ ha =>
    obtain ⟨m, a, γ, ha, rfl⟩ := ha
    refine ⟨m, fun k => c • a k, γ, fun k => ?_, ?_⟩
    · obtain ⟨m', f, g, hf, h⟩ := ha k
      refine ⟨m', fun j => c • f j, g, fun j => S.T'.smul_mem (hf j) c, ?_⟩
      funext x'
      simp [h, Finset.smul_sum, mul_smul]
    · simp [Finset.smul_sum]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem inCut_of_cocW (Xs : Set (D.nd.X i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i))
    (hψ : ∀ γ, ψ (fun x' => rTwO D.nd i r (S.p x') γ) = M γ)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (f : GE D.nd → KOG (D.nd.O i) k) (hf : f ∈ cocW i r S Xs ψ) : InCut i r Xs M w hw f := by
  unfold cocW at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨φ, h1, h0, rfl⟩ := hf
    obtain ⟨a, q, hq, E', Y, hY, hst, hE, φ', h2, h3⟩ :=
      factor (K := KK D.nd i) (IsFractionRing.injective _ _) (fun x' => S.p x' ∈ Xs)
        (fun x' => rTwO D.nd i r (S.p x')) (Eel D.nd S) (yg D.nd r S)
        (fun γ x' => by simp [yg, rTwO, twistM, sub_mul]) φ (fun γ => WKG M γ)
        (fun γ δ => by
          rw [h1 _ (inR'_tw i r S γ) _ (inY_yg i r S δ), hψ]
          obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (φ (yg D.nd r S δ))
          rw [← hu]
          rfl)
        (fun z hz => h0 z (inY_of_span i r S z hz))
    apply Submodule.subset_span
    refine ⟨a, fun j => S.p (q j), hq, E', Y, hY, hst, hE, φ', h2, ?_⟩
    funext g
    exact congrArg (Br.phi (D.nbr i w hw) k) (h3 _).symm
  | zero =>
    have e : locFun i M w hw 0 = 0 := by
      funext g
      exact (Br.phi (D.nbr i w hw) k).map_zero
    unfold InCut
    rw [e]
    exact Submodule.zero_mem _
  | add f f' _ _ h h' =>
    have e : locFun i M w hw (f + f') = locFun i M w hw f + locFun i M w hw f' := by
      funext g
      exact (Br.phi (D.nbr i w hw) k).map_add _ _
    unfold InCut at *
    rw [e]
    exact Submodule.add_mem _ h h'
  | smul c f _ h =>
    have e : locFun i M w hw (c • f) =
        ((D.nbr i w hw).eO c : Br.OLL D.nbr i w hw) • locFun i M w hw f := by
      funext g
      exact (Br.phi (D.nbr i w hw) k).map_smulₛₗ c _
    unfold InCut at *
    rw [e]
    exact Submodule.smul_mem _ _ h

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (∀ f ∈ cocRho i r S Xs, InCut i r Xs (WpO D.nd i ρ π) w hw f) ∧ ∀ c : Fin D.R.t, ∀ f ∈ cocChi i r S Xs c, InCut i r Xs (chiRatO D.nd i ((c : ℕ) + 1)) w hw f := by
  intro D i r ρ π Xs S _ hG _ w hw
  obtain ⟨-, hdec, hψ, -, -, -, -, -, -, ⟨hπ, -⟩, -⟩ := hG
  have key : ∀ γ u, (((S.ψρ fun x' => rTwO D.nd i r (S.p x') γ).map (toK D.nd i)).mulVec (S.e u).1,
      fun c : Fin D.R.t => toK D.nd i (S.ψχ c fun x' => rTwO D.nd i r (S.p x') γ) * (S.e u).2 c) =
      toK D.nd i (((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
        ((mapM (toK D.nd i) (rhoO D.nd i ρ π) γ).mulVec (S.e u).1,
        fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) γ : (D.nd.O i)ˣ) : D.nd.O i) * (S.e u).2 c) := by
    intro γ u
    rw [← hψ _ (inR'_tw i r S γ) u, ← hdec, ← map_smul, hπ, ← Matrix.smul_mulVec]
    congr 2
    ext p q
    simp [mapM, rTwO, twistM]
  refine ⟨fun f hf => inCut_of_cocW i r S Xs _ _ (fun γ => ?_) w hw f hf,
    fun c f hf => inCut_of_cocW i r S Xs _ _ (fun γ => ?_) w hw f hf⟩
  · ext p q
    apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
    have h := congrArg (fun z => z.1 p) (key γ (S.e.symm (Pi.single q 1, 0)))
    simpa [mapM, WpO, twistM] using h
  · ext p q
    apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
    have h := congrArg (fun z => z.2 c) (key γ (S.e.symm (0, Pi.single c 1)))
    obtain rfl : p = q := Subsingleton.elim _ _
    simpa [chiRatO, twistM, mul_comm] using h

end GlobalTheory.Cut.LocCoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixHomPeriodMatrixSemistable
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem kroneckerMap_mul_map_ringHom {R S : Type*} [CommRing R] [CommRing S] {a b : Type*} (f : R →+* S)
    (A : Matrix a a R) (B : Matrix b b R) :
    (Matrix.kroneckerMap (· * ·) A B).map f = Matrix.kroneckerMap (· * ·) (A.map f) (B.map f) := by
  ext p q
  simp [Matrix.kroneckerMap_apply]

theorem inv_periodMatrix_map_mul_eq_inv {S T : Type*} [CommRing S] [CommRing T] {b : Type*} [Fintype b] [DecidableEq b]
    (k : S →+* T) (σ : T →+* T) (r : GL b S) (Q : GL b T)
    (h : (r : Matrix b b S).map k * (Q : Matrix b b T).map σ = Q) :
    ((Q⁻¹ : GL b T) : Matrix b b T).map σ * ((r⁻¹ : GL b S) : Matrix b b S).map k = ((Q⁻¹ : GL b T) : Matrix b b T) := by
  have hQ : (Q : Matrix b b T) * (((Q⁻¹ : GL b T) : Matrix b b T).map σ * ((r⁻¹ : GL b S) : Matrix b b S).map k) = 1 := by
    rw [← h, Matrix.mul_assoc, ← Matrix.mul_assoc ((Q : Matrix b b T).map σ), ← Matrix.map_mul, Units.mul_inv,
      Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.one_mul, ← Matrix.map_mul, Units.mul_inv,
      Matrix.map_one _ (map_zero k) (map_one k)]
  calc ((Q⁻¹ : GL b T) : Matrix b b T).map σ * ((r⁻¹ : GL b S) : Matrix b b S).map k
      = ((Q⁻¹ : GL b T) : Matrix b b T) * (Q : Matrix b b T) *
          (((Q⁻¹ : GL b T) : Matrix b b T).map σ * ((r⁻¹ : GL b S) : Matrix b b S).map k) := by
        rw [Units.inv_mul, Matrix.one_mul]
    _ = ((Q⁻¹ : GL b T) : Matrix b b T) := by rw [Matrix.mul_assoc, hQ, Matrix.mul_one]

theorem homUnit_period : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (Q₁ : GL a (Bst P)) (Q₂ : GL b (Bst P)), (∀ g : ↥(GK K), (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₁ : Matrix a a (Bst P)).map (actSt P (g : GQ l)) = Q₁) → (∀ g : ↥(GK K), (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₂ : Matrix b b (Bst P)).map (actSt P (g : GQ l)) = Q₂) → ∀ g : ↥(GK K), (homRep ρ₁ ρ₂ g : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).map (ks P) * ((homUnit Q₁ Q₂ : GL (a × b) (Bst P)) : Matrix (a × b) (a × b) (Bst P)).map (actSt P (g : GQ l)) = (homUnit Q₁ Q₂ : GL (a × b) (Bst P)) := by
  intro l _ P a b _ _ _ _ K ρ₁ ρ₂ Q₁ Q₂ h₁ h₂ g
  set σ : Bst P →+* Bst P := (actSt P (g : GQ l)).toRingHom with hσ
  have e : ∀ {n : Type} (M : Matrix n n (Bst P)), M.map (actSt P (g : GQ l)) = M.map σ := fun M => rfl
  have h1 := h₁ g
  have h2 := h₂ g
  rw [e] at h1 h2
  rw [e, homRep_apply, homUnit_val, homUnit_val, kroneckerMap_mul_map_ringHom, kroneckerMap_mul_map_ringHom, ← Matrix.mul_kronecker_mul, h1,
    Matrix.transpose_map, Matrix.transpose_map, ← Matrix.transpose_mul, inv_periodMatrix_map_mul_eq_inv (ks P) σ (ρ₂ g) Q₂ h2]

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixHomRepresentationCocycleRationalContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section
open Matrix

namespace GlobalTheory.PMon

theorem matrixHomRepresentationCocycleCoords_cocycle {R : Type*} [CommRing R] {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {G : Type*} [Group G] (ρ : G →* GL (a ⊕ b) R) (ρ₁ : G →* GL a R) (ρ₂ : G →* GL b R) (c : G → Matrix a b R)
    (hρ : ∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) R) = Matrix.fromBlocks (ρ₁ g : Matrix a a R) (c g) 0 (ρ₂ g : Matrix b b R))
    (g h : G) :
    extCoc ρ₂ c (g * h) = extCoc ρ₂ c g + ((homRep ρ₁ ρ₂ g : GL (a × b) R) : Matrix (a × b) (a × b) R).mulVec (extCoc ρ₂ c h) := by
  have hc : c (g * h) = (ρ₁ g : Matrix a a R) * c h + c g * (ρ₂ h : Matrix b b R) := by
    have := congrArg (fun M : GL (a ⊕ b) R => Matrix.toBlocks₁₂ (M : Matrix (a ⊕ b) (a ⊕ b) R)) (map_mul ρ g h)
    simp only [Units.val_mul, hρ, Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₂] at this
    simpa using this
  unfold extCoc
  rw [homRep_apply, homUnit_val, kronecker_transpose_mulVec]
  rw [hc, map_mul, _root_.mul_inv_rev, Units.val_mul]
  have h2 : (ρ₂ h : Matrix b b R) * (((ρ₂ h)⁻¹ : GL b R) : Matrix b b R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Matrix.add_mul, Matrix.mul_assoc (c g), ← Matrix.mul_assoc (ρ₂ h : Matrix b b R), h2, Matrix.one_mul]
  funext p
  simp only [vecM, Pi.add_apply, Matrix.add_apply, Matrix.mul_assoc]
  ring

theorem extCoc_rat_cont_cocycle : ∀ (l : ℕ) [Fact l.Prime] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K K' : FinExt l) (hK : K.1 ≤ K'.1) (r : ℕ) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), IsRat r ρ → (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → (∀ g i, fr l r (extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g i) = extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g i) ∧ (∀ i, Continuous fun g => ((extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g i : ↥(MaximalUnramifiedExtension l)) : Om l)) ∧ (∀ g h, extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) (g * h) = extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) g + (homRep (ρ₁.comp (Subgroup.inclusion (GK_le hK))) (ρ₂.comp (Subgroup.inclusion (GK_le hK))) g : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).mulVec (extCoc (ρ₂.comp (Subgroup.inclusion (GK_le hK))) (fun g => c (Subgroup.inclusion (GK_le hK) g)) h)) := by
  intro l _ a b _ _ _ _ K K' hK r ρ ρ₁ ρ₂ c hrat hρ
  set ι := Subgroup.inclusion (GK_le hK) with hι
  have hent : ∀ g (i : a) (k : b), c g i k = (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inl i) (Sum.inr k) := by
    intro g i k; rw [hρ]; rfl
  have hinv : ∀ g (k j : b), (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)) k j =
      (ρ g⁻¹ : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr k) (Sum.inr j) := by
    intro g k j; rw [← map_inv, hρ]; rfl
  have hform : ∀ g (i : a × b), extCoc (ρ₂.comp ι) (fun g => c (ι g)) g i =
      ∑ k, (ρ (ι g) : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inl i.1) (Sum.inr k) *
        (ρ (ι g)⁻¹ : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr k) (Sum.inr i.2) := by
    intro g i
    simp only [extCoc, vecM, MonoidHom.comp_apply, Matrix.mul_apply, hent, hinv]
  have hcι : Continuous ι := Continuous.subtype_mk continuous_subtype_val _
  refine ⟨?_, ?_, ?_⟩
  · intro g i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hform, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hrat.rat, hrat.rat]
  · intro i
    have : (fun g => ((extCoc (ρ₂.comp ι) (fun g => c (ι g)) g i : ↥(MaximalUnramifiedExtension l)) : Om l)) = fun g =>
        ∑ k, (((ρ (ι g) : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inl i.1) (Sum.inr k) : ↥(MaximalUnramifiedExtension l)) : Om l) *
          (((ρ (ι g)⁻¹ : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr k) (Sum.inr i.2) : ↥(MaximalUnramifiedExtension l)) : Om l) := by
      funext g
      rw [hform]
      push_cast
      rfl
    rw [this]
    refine continuous_finsetSum _ fun k _ => ?_
    exact ((hrat.cont _ _).comp hcι).mul ((hrat.cont _ _).comp (continuous_inv.comp hcι))
  · intro g h
    exact matrixHomRepresentationCocycleCoords_cocycle (ρ.comp ι) (ρ₁.comp ι) (ρ₂.comp ι) (fun g => c (ι g)) (fun g => hρ (ι g)) g h

end GlobalTheory.PMon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixHomRepresentationRestrictRationalContinuou
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon

theorem isRat_homRep_restrict : ∀ (l : ℕ) [Fact l.Prime] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K K' : FinExt l) (hK : K.1 ≤ K'.1) (r : ℕ) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), IsRat r ρ → (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → IsRat r (homRep (ρ₁.comp (Subgroup.inclusion (GK_le hK))) (ρ₂.comp (Subgroup.inclusion (GK_le hK)))) := by
  intro l _ a b _ _ _ _ K K' hK r ρ ρ₁ ρ₂ c hρ hb
  set ι := Subgroup.inclusion (GK_le hK) with hι
  have e1 : ∀ g i j, (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) i j = (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inl i) (Sum.inl j) := by
    intro g i j; rw [hb]; rfl
  have e2 : ∀ g i j, (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)) i j = (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr i) (Sum.inr j) := by
    intro g i j; rw [hb]; rfl
  have key : ∀ g' p q, ((homRep (ρ₁.comp ι) (ρ₂.comp ι) g' : GL (a × b) ↥(MaximalUnramifiedExtension l)) : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)) p q =
      (ρ (ι g') : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inl p.1) (Sum.inl q.1) *
        (ρ (ι g')⁻¹ : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (Sum.inr q.2) (Sum.inr p.2) := by
    intro g' p q
    rw [homRep_apply, homUnit_val, Matrix.kroneckerMap_apply, Matrix.transpose_apply, ← map_inv, MonoidHom.comp_apply,
      MonoidHom.comp_apply, e1, e2, map_inv ι]
  have hιc : Continuous ι := continuous_subtype_val.subtype_mk _
  refine ⟨hρ.pos, fun x hx => hK (hρ.le x hx), ?_, ?_⟩
  · intro g p q
    rw [key, map_mul, hρ.rat, hρ.rat]
  · intro p q
    simp only [key, IntermediateField.coe_mul]
    exact ((hρ.cont _ _).comp hιc).mul ((hρ.cont _ _).comp (hιc.inv))

end GlobalTheory.PMon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaxUnramifiedOfCrystallineRatio
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.FracAlg

theorem ratio_adjoin {k Ω B D : Type} [Field k] [Field Ω] [Algebra k Ω] [CommRing B] [CommRing D] [IsDomain D]
    (ι : B →+* D) (hι : Function.Injective ι) (o : Ω →+* D)
    (hk : ∀ c : k, ∃ b : B, ι b = o (algebraMap k Ω c)) (x : Ω)
    (hx : ∃ a b : B, b ≠ 0 ∧ ι a = o x * ι b) (y : Ω) (hy : y ∈ IntermediateField.adjoin k {x}) :
    ∃ a b : B, b ≠ 0 ∧ ι a = o y * ι b := by
  have hne : ∀ b : B, b ≠ 0 → ι b ≠ 0 := fun b hb h => hb (hι (by rw [h, map_zero]))
  have hmul : ∀ b b' : B, b ≠ 0 → b' ≠ 0 → b * b' ≠ 0 := fun b b' hb hb' h =>
    mul_ne_zero (hne b hb) (hne b' hb') (by rw [← map_mul, h, map_zero])
  have h1 : (1 : B) ≠ 0 := fun h => one_ne_zero (α := D) (by rw [← map_one ι, h, map_zero])
  induction hy using IntermediateField.adjoin_induction with
  | mem z hz => rw [Set.mem_singleton_iff.1 hz]; exact hx
  | algebraMap c =>
    obtain ⟨b, hb⟩ := hk c
    exact ⟨b, 1, h1, by rw [hb, map_one, mul_one]⟩
  | add z w _ _ hz hw =>
    obtain ⟨a, b, hb, e⟩ := hz
    obtain ⟨a', b', hb', e'⟩ := hw
    refine ⟨a * b' + a' * b, b * b', hmul _ _ hb hb', ?_⟩
    simp only [map_add (f := _), map_mul, e, e']
    ring
  | inv z _ hz =>
    obtain ⟨a, b, hb, e⟩ := hz
    by_cases h0 : z = 0
    · exact ⟨0, 1, h1, by simp [h0]⟩
    · have ho : o z ≠ 0 := by simpa using h0
      refine ⟨b, a, fun h => mul_ne_zero ho (hne b hb) (by rw [← e, h, map_zero]), ?_⟩
      rw [e, ← mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, one_mul]
  | mul z w _ _ hz hw =>
    obtain ⟨a, b, hb, e⟩ := hz
    obtain ⟨a', b', hb', e'⟩ := hw
    refine ⟨a * a', b * b', hmul _ _ hb hb', ?_⟩
    simp only [map_mul, e, e']
    ring

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris


open GlobalTheory.MemLoc in
theorem norm_of_ratio {l : ℕ} [Fact l.Prime] (C : Core l) (a b : Per.Bcris l) (x : Om l) (hb : b ≠ 0)
    (hx : x ≠ 0) (e : C.ι a = C.oD x * C.ι b) : ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k := by
  obtain ⟨r, a', ha'⟩ := bcris_eq_acris_localization_periodT_alt l C a
  obtain ⟨s, b', hb'⟩ := bcris_eq_acris_localization_periodT_alt l C b
  have hu := (core_t_unit_fil l C).1
  have hA : algebraMap (Per.Acris l) (Per.Bcris l) (a' * C.t ^ s) =
      a * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ (r + s) := by
    rw [map_mul, map_pow, ← ha', pow_add, mul_assoc]
  have hB : algebraMap (Per.Acris l) (Per.Bcris l) (b' * C.t ^ r) =
      b * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ (r + s) := by
    rw [map_mul, map_pow, ← hb', add_comm r s, pow_add, mul_assoc]
  refine GlobalTheory.MemLoc.GaussCore.norm_eq_zpow l C (a' * C.t ^ s) (b' * C.t ^ r) x (fun h => hb ?_) hx ?_
  · rw [h, map_zero] at hB
    exact ((hu.pow _).mul_left_eq_zero).1 hB.symm
  · apply (BdRField.bdR_isField l).2.1
    rw [map_mul (algebraMap (Per.BdRp l) (Per.BdR l)), ← C.ι_j, ← C.ι_j, hA, hB, map_mul C.ι, map_mul C.ι, e,
      mul_assoc]
    rfl

end

theorem mem_Kur_of_ratio : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (a b : P.R.B) (x : Om l), b ≠ 0 → P.ιB a = algebraMap (Om l) P.R.BdR x * P.ιB b → x ∈ MaximalUnramifiedExtension l := by
  intro l _ P AI T a b x hb e
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨hF, -, hinj, -⟩ := GlobalTheory.Per.TiedField.tied_field l P AI T
  have : IsDomain P.R.BdR := hF.isDomain
  have hint : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral _
  refine GlobalTheory.UnramValue.le_Kur_of_norm l ⟨IntermediateField.adjoin ℚ_[l] {x}, IntermediateField.adjoin.finiteDimensional hint⟩
    (fun y hy hy0 => ?_) (IntermediateField.mem_adjoin_simple_self ℚ_[l] x)
  obtain ⟨a', b', hb', e'⟩ := ratio_adjoin (k := ℚ_[l]) (P.ιB : P.R.B →+* P.R.BdR) hinj
    (algebraMap (Om l) P.R.BdR)
    (fun c => ⟨algebraMap ℚ_[l] P.R.B c,
      (P.ιB.commutes c).trans (IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR c)⟩) x ⟨a, b, hb, e⟩ y hy
  refine norm_of_ratio C (T.eB a') (T.eB b') y (fun h => hb' (T.eB.injective (h.trans (map_zero _).symm))) hy0 ?_
  rw [← hC.ι, ← hC.ι, ← hC.o, ← map_mul]
  exact congrArg T.eD e'

end GlobalTheory.FracAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OcTensorCoeffBasisCoordsMemCyclotomicLevelOfPoweStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ocTensorCoeffBasisCoords_mem_cyclotomicLevel_of_powerSeries : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (m n f : ℕ) [NeZero n] (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (φ : LetA ↥(OL LL) n →+* OCO LL) (c : OC l), (∀ a : ↥(OL LL), φ (algebraMap ↥(OL LL) (LetA ↥(OL LL) n) a) = (1 : OC l) ⊗ₜ[ℤ_[l]] a) → φ letπ = c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) → ‖(c : PadicComplex l)‖ < 1 → (c : PadicComplex l) ∈ inC (Ks K m) → (∀ i k, kap o (φ (letE i)) k ∈ inC (Ks K m)) → ∀ a k, kap o (φ a) k ∈ intC (Ks K m) := by
  first | exact @GlobalTheory.Cyc.Decomp.Coord.coord | exact GlobalTheory.Cyc.Decomp.Coord.coord | (intros; apply GlobalTheory.Cyc.Decomp.Coord.coord <;> assumption)
end

