module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0324
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetGenericSumMemHeckeAlgebra
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.SpanRing

theorem charpoly_coeff_mem_of_charPolyIn {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ}
    (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)) (h : CharPolyIn T rep) (g : Γ) (j : ℕ) :
    (fun x => (mat (rep x) g).charpoly.coeff j) ∈ T := by
  unfold CharPolyIn at h
  rcases subsingleton_or_nontrivial O with hO | hO
  · have hz : (fun x => (mat (rep x) g).charpoly.coeff j) = 0 := Subsingleton.elim _ _
    rw [hz]
    exact T.zero_mem
  · by_cases hj : j ≤ n
    · have e : (fun x => (mat (rep x) g).charpoly.coeff j) =
          fun x => (mat (rep x) g).charpolyRev.coeff (n - j) := by
        funext x
        rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim,
          Fintype.card_fin, Polynomial.revAt_le (Nat.sub_le n j), Nat.sub_sub_self hj]
      rw [e]
      exact h g (n - j)
    · have hz : (fun x => (mat (rep x) g).charpoly.coeff j) = 0 := by
        funext x
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
        omega
      rw [hz]
      exact T.zero_mem

private theorem coeff_det_generic_sum_eval {X O : Type} [CommRing O] {n m : ℕ}
    (a : Fin m → X → Matrix (Fin n) (Fin n) O) (x : X) (d : Fin m →₀ ℕ) :
    AddMonoidAlgebra.coeff (Matrix.det (∑ k,
      (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) d =
    (AddMonoidAlgebra.coeff (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
      Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j)))) d : X → O) x := by
  set φ : MvPolynomial (Fin m) (X → O) →+* MvPolynomial (Fin m) O :=
    MvPolynomial.map (Pi.evalRingHom (fun _ => O) x) with hφ
  have h1 : φ.mapMatrix (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
      Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j))) =
      ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Matrix.ext fun i j => ?_
    simp [hφ]
  rw [← h1, ← RingHom.map_det, hφ, MvPolynomial.coeff_map]
  rfl

theorem coeff_det_generic_sum_mem_of_inRing :
    ∀ {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ} (T : Subalgebra O (X → O))
      (rep : X → (Γ →* GL (Fin n) O)), CharPolyIn T rep →
      ∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, InRing T rep (a k)) →
      ∀ d : Fin m →₀ ℕ, (fun x => AddMonoidAlgebra.coeff (Matrix.det (∑ k,
        (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) d) ∈ T := by
  intro Γ X O _ _ n T rep hT m a ha d
  classical

  let T' : Subring (MvPolynomial (Fin m) (X → O)) := (MvPolynomial.map T.val.toRingHom).range
  have hmemT : ∀ p ∈ T', ∀ e, AddMonoidAlgebra.coeff p e ∈ T := by
    intro p hp e
    obtain ⟨q, rfl⟩ := RingHom.mem_range.1 hp
    rw [MvPolynomial.coeff_map]
    exact (AddMonoidAlgebra.coeff q e).2
  have hC : ∀ f ∈ T, (MvPolynomial.C f : MvPolynomial (Fin m) (X → O)) ∈ T' := fun f hf =>
    RingHom.mem_range.2 ⟨MvPolynomial.C ⟨f, hf⟩, by simp⟩
  have hX : ∀ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) ∈ T' := fun k =>
    RingHom.mem_range.2 ⟨MvPolynomial.X k, by simp⟩

  let M : Γ → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O)) :=
    fun h => Matrix.of fun i j => MvPolynomial.C (fun y => mat (rep y) h i j)
  have hmul : ∀ A ∈ Set.range M, ∀ B ∈ Set.range M, A * B ∈ Set.range M := by
    rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
    refine ⟨g * h, ?_⟩
    refine Matrix.ext fun i j => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [M, Matrix.mul_apply, Matrix.of_apply, ← map_mul, ← map_sum]
    congr 1
    funext y
    simp [mat, Matrix.mul_apply, Finset.sum_apply]
  have hchar : ∀ A ∈ Set.range M, ∀ j, A.charpoly.coeff j ∈ T' := by
    rintro _ ⟨h, rfl⟩ j
    have hP : M h = (Matrix.of fun i j => fun y => mat (rep y) h i j).map MvPolynomial.C := by
      refine Matrix.ext fun i j => ?_
      rfl
    rw [hP, Matrix.charpoly_map, Polynomial.coeff_map]
    apply hC
    have e : (Matrix.of fun i j => fun y => mat (rep y) h i j).charpoly.coeff j =
        fun y => (mat (rep y) h).charpoly.coeff j := by
      funext y
      have hm : (Matrix.of fun i j => fun y => mat (rep y) h i j).map (Pi.evalRingHom (fun _ => O) y) =
          mat (rep y) h := by
        refine Matrix.ext fun i j => ?_
        rfl
      have e' := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p j)
        (Matrix.charpoly_map (Matrix.of fun i j => fun y => mat (rep y) h i j) (Pi.evalRingHom (fun _ => O) y))
      rw [hm] at e'
      simp only [Polynomial.coeff_map] at e'
      exact e'.symm
    rw [e]
    exact charpoly_coeff_mem_of_charPolyIn T rep hT h j

  have hlift : ∀ b : X → Matrix (Fin n) (Fin n) O, b ∈ Submodule.span O (gens T rep) →
      (Matrix.of fun i j => MvPolynomial.C (fun y => b y i j) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O)))
        ∈ Submodule.span T' (Set.range M) := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨f, hf, h, rfl⟩ := hb
      have e : (Matrix.of fun i j => MvPolynomial.C (fun y => (fun x => f x • mat (rep x) h) y i j) :
          Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) =
          (⟨MvPolynomial.C f, hC f hf⟩ : T') • M h := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.of_apply, Subring.smul_def, Matrix.smul_apply, smul_eq_mul, M, ← map_mul]
        congr 1
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)
    | zero =>
      have e : (Matrix.of fun i j => MvPolynomial.C (fun y => (0 : X → Matrix (Fin n) (Fin n) O) y i j) :
          Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) = 0 := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.of_apply, Pi.zero_apply, Matrix.zero_apply]
        exact map_zero _
      rw [e]
      exact Submodule.zero_mem _
    | add b c _ _ hb hc =>
      have e : (Matrix.of fun i j => MvPolynomial.C (fun y => (b + c) y i j) :
          Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) =
          Matrix.of (fun i j => MvPolynomial.C (fun y => b y i j)) +
            Matrix.of (fun i j => MvPolynomial.C (fun y => c y i j)) := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.of_apply, Matrix.add_apply, ← map_add (f := _)]
        rfl
      rw [e]
      exact Submodule.add_mem _ hb hc
    | smul r b _ hb =>
      have e : (Matrix.of fun i j => MvPolynomial.C (fun y => (r • b) y i j) :
          Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) =
          (⟨MvPolynomial.C (algebraMap O (X → O) r), hC _ (T.algebraMap_mem r)⟩ : T') •
            Matrix.of (fun i j => MvPolynomial.C (fun y => b y i j)) := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.of_apply, Subring.smul_def, Matrix.smul_apply, smul_eq_mul, ← map_mul]
        congr 1
      rw [e]
      exact Submodule.smul_mem _ _ hb
  have hB : (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
      Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j))) ∈ Submodule.span T' (Set.range M) := by
    refine Submodule.sum_mem _ fun k _ => ?_
    have := Submodule.smul_mem (Submodule.span T' (Set.range M)) (⟨MvPolynomial.X k, hX k⟩ : T')
      (hlift (a k) ((inRing_iff_mem_span T rep (a k)).1 (ha k)))
    exact this
  obtain ⟨N, f, g, hfg⟩ := Submodule.mem_span_set'.1 hB
  have hdet := Amitsur.det_sum_smul_mem T' (Set.range M) hmul hchar Finset.univ
    (fun i => (f i : MvPolynomial (Fin m) (X → O))) (fun i => (g i).1)
    (fun i => (f i).2) (fun i => (g i).2)
  have hsum : (∑ i ∈ Finset.univ, (f i : MvPolynomial (Fin m) (X → O)) • (g i).1) =
      ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
        Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j)) := by
    rw [← hfg]
    rfl
  rw [hsum] at hdet
  have key : (fun x => AddMonoidAlgebra.coeff (Matrix.det (∑ k,
      (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) d) =
      AddMonoidAlgebra.coeff (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
        Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j)))) d :=
    funext fun x => coeff_det_generic_sum_eval a x d
  rw [key]
  exact hmemT _ hdet d

end GlobalTheory.SpanRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousWittCbInclusionSmulWeakTopology
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.WeakClosed

theorem continuous_io_smul_of {O RA RW M : Type} [CommRing O] [TopologicalSpace O] [CommRing RA]
    [Algebra O RA] [CommRing RW] [Algebra O RW] [AddCommGroup M] [Module RW M] [Module O M]
    [IsScalarTower O RW M] [TopologicalSpace M] [IsTopologicalAddGroup M] {n : ℕ}
    (io : LetA O n →ₐ[O] RA) (inc : RA →ₐ[O] RW) (y : M) (πA : RA) (hπ : io letπ = πA)
    (hsmall : ∀ U ∈ 𝓝 (0 : M), ∃ k : ℕ, ∀ z : RA, inc (πA ^ k * z) • y ∈ U)
    (hlin : ∀ f : (ZMod n → O) →ₗ[O] M, Continuous f) :
    Continuous fun a : LetA O n => inc (io a) • y := by
  let Φ : LetA O n →+ M :=
    { toFun := fun a => inc (io a) • y
      map_zero' := by simp
      map_add' := fun a c => by simp [add_smul] }
  refine GlobalTheory.T.continuous_of_tail_small_of_monomial_continuous Φ ?_ ?_
  · intro U hU
    obtain ⟨k, hk⟩ := hsmall U hU
    refine ⟨k, fun r => ?_⟩
    have hΦ : Φ (letπ ^ k * r) = inc (πA ^ k * io r) • y := by
      show inc (io (letπ ^ k * r)) • y = _
      rw [map_mul, map_pow, hπ]
    rw [hΦ]
    exact hk _
  · intro j
    let f : (ZMod n → O) →ₗ[O] M :=
      { toFun := fun c => inc (io (fun i => PowerSeries.C (c i))) • (inc (io letπ) ^ j • y)
        map_add' := fun c c' => by
          have : (fun i => PowerSeries.C ((c + c') i)) =
              (fun i => PowerSeries.C (c i)) + fun i => PowerSeries.C (c' i) := by
            funext i; simp
          simp only [this, map_add (f := _), add_smul]
        map_smul' := fun o c => by
          have : (fun i => PowerSeries.C ((o • c) i)) = o • (fun i => PowerSeries.C (c i)) := by
            funext i; simp [PowerSeries.smul_eq_C_mul, map_mul]
          simp only [this, map_smul, smul_assoc, RingHom.id_apply] }
    refine (hlin f).congr fun c => ?_
    have hc : (fun i => PowerSeries.C (c i) * PowerSeries.X ^ j : LetA O n) =
        (fun i => PowerSeries.C (c i)) * letπ ^ j := by
      funext i; simp [letπ]
    show inc (io (fun i => PowerSeries.C (c i))) • (inc (io letπ) ^ j • y) =
      inc (io (fun i => PowerSeries.C (c i) * PowerSeries.X ^ j)) • y
    rw [hc, map_mul, map_mul, mul_smul, map_pow, map_pow]

end GlobalTheory.WeakClosed

namespace GlobalTheory.WeakClosed

theorem isTopologicalAddGroup_twTop {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (T : Lt K LL) {d : ℕ}
    (b : LatB T d) : letI := twTop T b; IsTopologicalAddGroup (TW (RW LL) T) := by
  letI := cbValued l
  letI := zlMod T
  haveI := zlTower T
  letI : TopologicalSpace (WCb l) := wTop l
  letI : TopologicalSpace (TW (RW LL) T) := twTop T b
  haveI : IsTopologicalRing (Cb l) := inferInstance
  haveI : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  exact Topology.IsInducing.topologicalAddGroup (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b) ⟨rfl⟩

theorem finrank_maxUnramifiedSubfield_pos {l : ℕ} [Fact l.Prime] (K : FinExt l) : 0 < Module.finrank ℚ_[l] ↥(K0 K) := by
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] (K0 K) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (RingHom.injective _)
  exact Module.finrank_pos

theorem continuous_inclR_io_smul : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l} {h : Good K s LL} {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))} (E : EtSit P AI K s LL h W) (T : Lt K LL) {d e : ℕ} (b : LatB T d) (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)) (y : TW (RW LL) T), letI := twTop T b; letI := aTop (K := K) bO; Continuous fun a : AA K LL => inclR LL (E.tie.io a) • y := by
  intro l _ P AI K s LL h W E T d e b bO y
  letI tT : TopologicalSpace (TW (RW LL) T) := twTop T b
  letI tO : TopologicalSpace ↥(OL LL) := oTop bO
  haveI := isTopologicalAddGroup_twTop T b
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨(finrank_maxUnramifiedSubfield_pos K).ne'⟩
  have hlin : ∀ f : (ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL)) →ₗ[↥(OL LL)] TW (RW LL) T,
      Continuous f := fun f => GlobalTheory.T.continuous_linearMap_pi_of_continuous_coord bO (GlobalTheory.T.continuous_padicInt_smul_latB T b) f
  haveI : IsScalarTower ↥(OL LL) (RW LL) (TW (RW LL) T) :=
    TensorProduct.isScalarTower_left (R := ↥(OL LL)) (M := RW LL) (N := ↥T.L.T)
      (R' := RW LL) (R'₂ := ↥(OL LL))
  exact continuous_io_smul_of E.tie.io (inclR LL) y _ E.tie.io_π (GlobalTheory.T.exists_pow_inclR_smul_mem' AI s T b y) hlin

end GlobalTheory.WeakClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoversAction
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.BKGal.CoversConv

open GlobalTheory.BKReal

variable {l : ℕ} [Fact l.Prime]

def toOC (LL : FinExt l) : OA l ↥(OL LL) →+* OC l :=
  letI : Algebra ℤ_[l] (OC l) := ((Per.θ l).comp (algebraMap ℤ_[l] (Ainf l))).toAlgebra
  (Algebra.TensorProduct.lift (R := ℤ_[l]) (S := ℤ_[l])
    ({ intToOC LL with commutes' := fun z => intToOC_algebraMap LL z } : ↥(OL LL) →ₐ[ℤ_[l]] OC l)
    ({ Per.θ l with commutes' := fun _ => rfl } : Ainf l →ₐ[ℤ_[l]] OC l)
    (fun _ _ => Commute.all _ _)).toRingHom

theorem toOC_tmul (LL : FinExt l) (o : ↥(OL LL)) (x : Ainf l) :
    toOC LL (o ⊗ₜ x) = intToOC LL o * Per.θ l x := rfl

theorem toOC_constA (a : ℕ) [NeZero a] (LL : FinExt l) [HasUnr a LL] (c : ZMod a → ↥(OL LL)) :
    toOC LL (constA (thetaW a LL) c) = intToOC LL (c 0) := by
  obtain ⟨y, rfl⟩ := (splitHom_bijective (thetaW a LL)).2 c
  rw [constA_splitHom]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, toOC_tmul, splitHom_tmul, emb_zero, map_mul,
      intToOC_thetaW]
  | add y y' h h' => simp only [map_add (f := _), Pi.add_apply, h, h']

theorem iTot_const {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] {a e : ℕ} [NeZero a]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (c : ZMod a → O) :
    ϖ.iTot t K (fun τ => algebraMap O (A O K) (c τ)) = constA t c := by
  rw [PiSys.iTot, glue_apply, eq_sum_idem]
  simp only [AlgHom.commutes]

end GlobalTheory.BKGal.CoversConv


open GlobalTheory.BKGal.CoversConv GlobalTheory.BKReal in
theorem GlobalTheory.BKGal.covers_action : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (k : GQ l) (γ : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ k γ → (∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ γ.shift.val) ∧ k (ϖ.seq 0) = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0 := by
  intro l _ a e _ _ ϖ LL _ _ k γ hc
  set t := thetaW a LL with ht
  have hW : ∀ w : Wq l a, Per.σO k (Per.θ l (wA l a w)) =
      Per.θ l (wA l a ((sigma l a ^ γ.shift.val) w)) := by
    intro w
    have h1 := hc (fun τ => algebraMap _ (A ↥(OL LL) ↥LL.1) (emb t τ w))
      (fun τ => algebraMap _ (A ↥(OL LL) ↥LL.1) (emb t (τ - γ.shift) w)) (fun τ => by
        change _ = rescale (γ.root τ) _
        beta_reduce
        have hC : ∀ (c : ↥(OL LL)) (m : ℕ), coeff m ((algebraMap _ (A ↥(OL LL) ↥LL.1) c : A _ _) : (↥LL.1)⟦X⟧) =
            if m = 0 then algebraMap _ ↥LL.1 c else 0 := fun c m =>
          (congrArg (coeff m) (GlobalTheory.BK.algebraMap_eq_C (K := ↥LL.1) c)).trans (coeff_C ..)
        ext1 n
        rw [coeff_rescale, hC]
        split_ifs with h
        · rw [h, pow_zero, one_mul]
        · rw [mul_zero])
    rw [iTot_const, iTot_const, constA_emb, galOA_tmul] at h1
    have h2 := congrArg (toOC LL) h1
    rw [toOC_tmul, toOC_constA, map_one, one_mul, GlobalTheory.RingBasics.θ_σA] at h2
    rw [h2, ← intToOC_thetaW a LL]
    congr 1
    show t ((sigma l a ^ (-(0 - γ.shift)).val) w) = _
    rw [zero_sub, neg_neg]
  obtain ⟨z, ω, hω, hz, -⟩ := exists_gen l a
  have hpow : ∀ j : ℕ, ((Per.θ l (wA l a (WittVector.teichmuller l (z ^ j))) : OC l) : ℂ_[l]) =
      ((ω ^ j : Om l) : ℂ_[l]) := by
    intro j
    rw [wA_teich, WittVector.fontaineTheta_teichmuller, map_pow, map_pow, SubmonoidClass.coe_pow,
      GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz]
    first
    | exact (map_pow (algebraMap (Om l) ℂ_[l]) ω j).symm
    | norm_cast
    | exact (UniformSpace.Completion.coe_pow ..).symm
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases eq_or_ne x 0 with rfl | hx0
    · rw [map_zero, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]
    · have h1 := one_lt_pow_l l a
      have : NeZero (l ^ a - 1) := ⟨by omega⟩
      have hx1 : x ^ (l ^ a - 1) = 1 := mul_right_cancel₀ hx0 (by
        rw [← pow_succ, Nat.sub_add_cancel h1.le, hx, one_mul])
      obtain ⟨j, -, rfl⟩ := hω.eq_pow_of_pow_eq_one hx1
      have h2 := congrArg (fun y : OC l => (y : ℂ_[l])) (hW (WittVector.teichmuller l (z ^ j)))
      rw [sigma_pow_teich, map_pow (wA l a), map_pow (Per.θ l), SubmonoidClass.coe_pow, hpow] at h2
      replace h2 := (GlobalTheory.RingIface.sigO_coe l k _).symm.trans h2
      rw [hpow, GlobalTheory.RingBasics.σC_coe] at h2
      exact (algebraMap (Om l) ℂ_[l]).injective (h2.trans (map_pow (algebraMap (Om l) ℂ_[l]) _ _).symm)
  · have hr : ∀ τ, IsIntegral ℤ_[l] (γ.root τ) := fun τ =>
      IsIntegral.of_pow (NeZero.pos e) (by rw [γ.root_pow]; exact isIntegral_one)
    let r : ZMod a → ↥(OL LL) := fun τ => ⟨γ.root τ, hr τ⟩
    have h1 := hc (fun _ => uIn (A ↥(OL LL) ↥LL.1))
      ((fun τ => algebraMap _ (A ↥(OL LL) ↥LL.1) (r τ)) * fun _ => uIn (A ↥(OL LL) ↥LL.1)) (fun τ => by
        change ((algebraMap _ (A ↥(OL LL) ↥LL.1) (r τ) : A _ _) : (↥LL.1)⟦X⟧) *
          ((uIn (A ↥(OL LL) ↥LL.1) : A _ _) : (↥LL.1)⟦X⟧) =
          rescale (γ.root τ) ((uIn (A ↥(OL LL) ↥LL.1) : A _ _) : (↥LL.1)⟦X⟧)
        rw [coe_uIn, rescale_X]
        exact congrArg (· * X) (GlobalTheory.BK.algebraMap_eq_C (K := ↥LL.1) (r τ)))
    rw [map_mul (ϖ.iTot t ↥LL.1), iTot_const, PiSys.iTot_u, galOA_tmul] at h1
    have h2 := congrArg (toOC LL) h1
    rw [map_mul (toOC LL), toOC_tmul, toOC_constA, toOC_tmul, map_one, one_mul, one_mul, GlobalTheory.RingBasics.θ_σA,
      PiSys.theta_teich] at h2
    have h3 := (GlobalTheory.RingIface.sigO_coe l k (ϖ.seqO 0)).symm.trans (congrArg (fun y : OC l => (y : ℂ_[l])) h2)
    have h4 := (GlobalTheory.RingBasics.σC_coe k (ϖ.seq 0)).symm.trans h3
    have hr0 : ((r 0 : ↥LL.1) : Om l) = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) := by
      simp [r, TameGal.root]
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [map_mul (algebraMap (Om l) ℂ_[l]), ← hr0]
    exact h4
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalCoordinatesConstantCoeffEq
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysConst

theorem semi_ext {A B C M N : Type} [CommRing A] [CommRing B] [CommRing C] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) (k : B →+* C)
    (F G : N →+ C) (hF : ∀ (r : B) y, F (r • y) = k r * F y) (hG : ∀ (r : B) y, G (r • y) = k r * G y)
    (hx : ∀ x, F (u x) = G (u x)) (y : N) : F y = G y := by
  letI : Module B C := Module.compHom C k
  let F' : N →ₗ[B] C := { toFun := F, map_add' := F.map_add, map_smul' := hF }
  let G' : N →ₗ[B] C := { toFun := G, map_add' := G.map_add, map_smul' := hG }
  exact LinearMap.congr_fun (h.hom_ext (w := F') (w' := G') hx) y

theorem semi_lift {A B C M N : Type} [CommRing A] [CommRing B] [CommRing C] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) (k : B →+* C)
    (F : M →+ C) (hF : ∀ (r : A) x, F (r • x) = k (f r) * F x) :
    ∃ G : N →+ C, (∀ (r : B) y, G (r • y) = k r * G y) ∧ ∀ x, G (u x) = F x := by
  letI : Module B C := Module.compHom C k
  let F' : M →ₛₗ[f] C := { toFun := F, map_add' := F.map_add, map_smul' := hF }
  obtain ⟨w, hw, -⟩ := h C F'
  exact ⟨w.toAddMonoidHom, fun r y => w.map_smul r y, hw⟩

theorem eq_of_diagonal {l : ℕ} {R C : Type} [CommRing R] [CommRing C] (E : FCrys l R) {P PP S : Obj l R}
    (p₀ p₁ : GlobalTheory.Prism.Hom P PP) (δ : GlobalTheory.Prism.Hom PP S) (hδ : δ.comp p₀ = δ.comp p₁) (k : S.A →+* C)
    (F G : E.M PP →+ C) (hF : ∀ (r : PP.A) y, F (r • y) = k (δ.f r) * F y)
    (hG : ∀ (r : PP.A) y, G (r • y) = k (δ.f r) * G y)
    (hx : ∀ x, F (E.tr p₀ x) = G (E.tr p₁ x)) (y : E.M PP) : F y = G y := by
  obtain ⟨μ, hμ, hμx⟩ := semi_lift (E.tr_bc (δ.comp p₀)) k (F.comp (E.tr p₀).toAddMonoidHom) (fun r x => by
    change F (E.tr p₀ (r • x)) = k (δ.f (p₀.f r)) * F (E.tr p₀ x)
    rw [LinearMap.map_smulₛₗ, hF])
  have hν : ∀ (r : PP.A) y, (μ.comp (E.tr δ).toAddMonoidHom) (r • y) =
      (k.comp δ.f) r * (μ.comp (E.tr δ).toAddMonoidHom) y := fun r y => by
    change μ (E.tr δ (r • y)) = k (δ.f r) * μ (E.tr δ y)
    rw [LinearMap.map_smulₛₗ, hμ]
  have h0 := semi_ext (E.tr_bc p₀) (k.comp δ.f) F _ hF hν (fun x => by
    change _ = μ (E.tr δ (E.tr p₀ x))
    rw [← E.tr_comp, hμx]; rfl) y
  have h1 := semi_ext (E.tr_bc p₁) (k.comp δ.f) G _ hG hν (fun x => by
    change _ = μ (E.tr δ (E.tr p₁ x))
    rw [← E.tr_comp, ← hx]
    have : ∀ q : GlobalTheory.Prism.Hom P S, δ.comp p₀ = q → μ (E.tr q x) = F (E.tr p₀ x) := by
      rintro _ rfl
      exact hμx x
    exact (this _ hδ).symm) y
  exact h0.trans h1.symm

theorem constantCoeff_eq : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (GlobalTheory.BKReal.toAc t K w τ : K⟦X⟧) * c x τ i) → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ (PP S₀ : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (δ : GlobalTheory.Prism.Hom PP S₀) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (j₀ : ZMod a → S₀.A →+* K⟦X⟧), δ.comp p₀ = δ.comp p₁ → (∀ τ y, j₀ τ (δ.f y) = PowerSeries.constantCoeff (j τ y)) → (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (GlobalTheory.BKReal.toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (GlobalTheory.BKReal.toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (lam₀ lam₁ : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧)), (∀ (r : PP.A) (y : EE.M PP) τ i, lam₀ (r • y) τ i = j τ r * lam₀ y τ i) → (∀ (r : PP.A) (y : EE.M PP) τ i, lam₁ (r • y) τ i = j τ r * lam₁ y τ i) → (∀ x τ i, lam₀ (EE.tr p₀ x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → (∀ x τ i, lam₁ (EE.tr p₁ x) τ i = sh (frob K l (c x (τ - 1) i))) → ∀ y τ i, PowerSeries.constantCoeff (lam₀ y τ i) = PowerSeries.constantCoeff (lam₁ y τ i) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ EE c _ sh hsh PP S₀ p₀ p₁ δ j j₀ hδ hj _ lam₀ lam₁ h₀ h₁ hx₀ hx₁
    y τ i
  have hc : ∀ f : K⟦X⟧, PowerSeries.constantCoeff (sh f) = f := fun f => by
    simpa using hsh f 0
  let pr : (ZMod a → ι → K⟦X⟧⟦X⟧) →+ K⟦X⟧ :=
    { toFun := fun q => PowerSeries.constantCoeff (q τ i)
      map_zero' := by simp
      map_add' := fun q q' => by simp }
  refine eq_of_diagonal EE p₀ p₁ δ hδ (j₀ τ) (pr.comp lam₀) (pr.comp lam₁) (fun r y => ?_) (fun r y => ?_)
    (fun x => ?_) y
  · change PowerSeries.constantCoeff (lam₀ (r • y) τ i) = _ * PowerSeries.constantCoeff (lam₀ y τ i)
    rw [h₀, map_mul, hj]
  · change PowerSeries.constantCoeff (lam₁ (r • y) τ i) = _ * PowerSeries.constantCoeff (lam₁ y τ i)
    rw [h₁, map_mul, hj]
  · change PowerSeries.constantCoeff (lam₀ (EE.tr p₀ x) τ i) = PowerSeries.constantCoeff (lam₁ (EE.tr p₁ x) τ i)
    rw [hx₀, hx₁, hc, PowerSeries.constantCoeff_C]

end GlobalTheory.CrysConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_breuilKisin_module_basis_of_fCrystal : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (T : Lat a O K ϖ), (letI := zlLat T; ∃ E : FCrys l ↥(OL (ϖ.field a)), IsRealisation (ϖ.field a) E ↥T.L.T (actZ T)) → Nonempty (BKMod t ϖ T) := by
  first | exact @GlobalTheory.BKReal.OfCrystal.main | exact GlobalTheory.BKReal.OfCrystal.main | (intros; apply GlobalTheory.BKReal.OfCrystal.main <;> assumption)
end

