module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0100
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.Bundle0001
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
public import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.PtStep0
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WordFreeNumberLeOrbitBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardOrbitSeriesValuationBoundZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KvalGeOrbitGainWithoutOperator
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralFiniteAdelesTensorIffLocalOrders
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

namespace GlobalTheory.PlaceComp.IntLocal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_int_generators (E : Type) [Field E] [NumberField E] :
    ∃ (k : ℕ) (x : Fin k → 𝓞 E), ∀ w : 𝓞 E, ∃ n : Fin k → ℤ, w = ∑ j, n j • x j := by
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  refine ⟨k, s, fun w => ?_⟩
  have : w ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
  exact ⟨n, hn.symm⟩


omit [NumberField E] in
theorem mem_addClosure_of_mem_ordAt (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E)
    (hy : y ∈ ordAt E v) :
    y ∈ AddSubgroup.closure
      {y : Fv F v ⊗[F] E | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} := by
  have h := Subring.mem_closure_iff.1 hy
  refine AddSubgroup.closure_mono ?_ h
  intro z hz
  induction hz using Submonoid.closure_induction with
  | mem z hz => exact hz
  | one => exact ⟨1, one_mem _, 1, rfl⟩
  | mul z w _ _ hz hw =>
    obtain ⟨a, ha, x, rfl⟩ := hz
    obtain ⟨b, hb, x', rfl⟩ := hw
    exact ⟨a * b, mul_mem ha hb, x * x', by
      rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl⟩


omit [NumberField E] in
theorem exists_coeff {k : ℕ} (x : Fin k → 𝓞 E)
    (hx : ∀ w : 𝓞 E, ∃ n : Fin k → ℤ, w = ∑ j, n j • x j) (v : HeightOneSpectrum (𝓞 F))
    (y : Fv F v ⊗[F] E) (hy : y ∈ ordAt E v) :
    ∃ a : Fin k → Fv F v, (∀ j, a j ∈ v.adicCompletionIntegers F) ∧
      y = ∑ j, a j ⊗ₜ[F] (x j : E) := by
  have hy' := mem_addClosure_of_mem_ordAt v y hy
  clear hy
  induction hy' using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, w, rfl⟩ := hy
    obtain ⟨n, rfl⟩ := hx w
    refine ⟨fun j => n j • a, fun j => zsmul_mem ha _, ?_⟩
    show a ⊗ₜ[F] (algebraMap (𝓞 E) E (∑ j, n j • x j)) =
      ∑ j, (n j • a) ⊗ₜ[F] (algebraMap (𝓞 E) E (x j))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.smul_tmul]
  | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, ea⟩ := hy
    obtain ⟨b, hb, eb⟩ := hz
    exact ⟨a + b, fun j => add_mem (ha j) (hb j), by
      simp only [Pi.add_apply, ea, eb, TensorProduct.add_tmul, Finset.sum_add_distrib]⟩
  | neg y _ hy =>
    obtain ⟨a, ha, ea⟩ := hy
    exact ⟨-a, fun j => neg_mem (ha j), by
      simp only [Pi.neg_apply, ea, TensorProduct.neg_tmul, Finset.sum_neg_distrib]⟩

theorem mem_intA_iff :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (z : Af F ⊗[F] E),
      z ∈ intA F E ↔ ∀ v : HeightOneSpectrum (𝓞 F), evF E v z ∈ ordAt E v := by
  intro F E _ _ _ _ _ z
  constructor
  · intro hz v
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      exact Subring.subset_closure ⟨_, ha v, x, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg]; exact neg_mem hy
  · intro h
    obtain ⟨k, x, hx⟩ := exists_int_generators E
    choose a ha ea using fun v => exists_coeff x hx v _ (h v)
    let A : Fin k → Af F := fun j =>
      ⟨fun v => a v j, Filter.Eventually.of_forall fun v => ha v j⟩
    have e : z = ∑ j, A j ⊗ₜ[F] (x j : E) := by
      apply evF_ext
      intro v
      set_option synthInstance.maxHeartbeats 100000 in
        rw [ea v, map_sum]
      exact Finset.sum_congr rfl fun j _ => rfl
    rw [e]
    exact sum_mem fun j _ => AddSubgroup.subset_closure ⟨A j, fun v => ha v j, x j, rfl⟩

end GlobalTheory.PlaceComp.IntLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulVecMemColSpan
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.UG Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct Matrix

namespace GlobalTheory.TwV.LbB

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {p n : ℕ} {G : GAtP p}

def FrAtB (A : LocAt F E n G) (Lb : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  ∀ v (t : Fin n → (A.pl v).1.adicCompletion F),
    (∃ x ∈ Formalism.L2.Herm.locL (A.pl v).1 Lb, ∀ a, (A.spl v (x a)).1 = t a) ↔
      ∀ a, ((((bc (A.phE v) A.B)⁻¹ : GL (Fin n) ((A.pl v).1.adicCompletion F)) :
        Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) *ᵥ t) a ∈ (A.pl v).1.adicCompletionIntegers F

def IntB (A : LocAt F E n G) (v : Fin G.P.nV) (t : Fin n → G.P.Qq v) : Prop :=
  ∀ a, ((((bc (A.phE v) A.B)⁻¹ : GL (Fin n) ((A.pl v).1.adicCompletion F)) :
    Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) *ᵥ (fun k => A.eQ v (t k))) a ∈ (A.pl v).1.adicCompletionIntegers F

theorem intB_zero (A : LocAt F E n G) (v : Fin G.P.nV) : IntB A v 0 := by
  intro a
  have : (fun k => A.eQ v ((0 : Fin n → G.P.Qq v) k)) = 0 := by funext k; simp
  rw [this, Matrix.mulVec_zero]
  exact zero_mem _

theorem intB_add (A : LocAt F E n G) (v : Fin G.P.nV) (t t' : Fin n → G.P.Qq v) (h : IntB A v t) (h' : IntB A v t') :
    IntB A v (t + t') := by
  intro a
  have : (fun k => A.eQ v ((t + t') k)) = (fun k => A.eQ v (t k)) + (fun k => A.eQ v (t' k)) := by funext k; simp
  rw [this, Matrix.mulVec_add]
  exact add_mem (h a) (h' a)

theorem intB_smul (A : LocAt F E n G) (hW : LocInt A) (v : Fin G.P.nV) (c : G.P.W v) (t : Fin n → G.P.Qq v) (h : IntB A v t) :
    IntB A v (c • t) := by
  intro a
  have : (fun k => A.eQ v ((c • t) k)) = A.eQ v (algebraMap (G.P.W v) (G.P.Qq v) c) • (fun k => A.eQ v (t k)) := by
    funext k
    rw [Pi.smul_apply, Algebra.smul_def, map_mul]
    rfl
  rw [this, Matrix.mulVec_smul]
  exact mul_mem ((hW v _).1 ⟨c, rfl⟩) (h a)

theorem mulVec_inv_mulVec {R : Type} [CommRing R] (y : GL (Fin n) R) (u : Fin n → R) :
    (y : Matrix (Fin n) (Fin n) R) *ᵥ (((y⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ u) = u := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem mulVec_mem_colSpan {Qq W : Type} [CommRing W] [Field Qq] [Algebra W Qq] (M : Matrix (Fin n) (Fin n) Qq) (r : Fin n → W) :
    M *ᵥ (fun c => algebraMap W Qq (r c)) ∈ colSpan W M := by
  have : M *ᵥ (fun c => algebraMap W Qq (r c)) = ∑ c, r c • (fun i => M i c) := by
    funext i
    rw [Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Algebra.smul_def, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem fst_mem_span (A : LocAt F E n G) (hW : LocInt A)
    (hAlg : ∀ v (a : (A.pl v).1.adicCompletion F), A.spl v ((1 : E) ⊗ₜ[F] a) = (a, a)) (v : Fin G.P.nV)
    (Lb : Submodule (𝓞 E) (Fin n → E)) (x : Fin n → E ⊗[F] (A.pl v).1.adicCompletion F)
    (hx : x ∈ Formalism.L2.Herm.locL (A.pl v).1 Lb) :
    (fun a => (A.eQ v).symm ((A.spl v (x a)).1)) ∈
      Submodule.span (G.P.W v) ((fun x : Fin n → E => fun k => A.iw v (x k)) '' (Lb : Set (Fin n → E))) := by
  unfold Formalism.L2.Herm.locL latS at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, hy, rfl⟩ := hz
    exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero =>
    have : (fun a => (A.eQ v).symm ((A.spl v ((0 : Fin n → E ⊗[F] (A.pl v).1.adicCompletion F) a)).1)) = 0 := by
      funext a; simp
    rw [this]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : (fun a => (A.eQ v).symm ((A.spl v ((x + y) a)).1)) =
        (fun a => (A.eQ v).symm ((A.spl v (x a)).1)) + (fun a => (A.eQ v).symm ((A.spl v (y a)).1)) := by
      funext a; simp
    rw [this]
    exact Submodule.add_mem _ hx hy
  | smul s x _ hx =>
    have hs := (split_integral_completion F E (A.pl v).1 (A.spl v) (hAlg v) s).1 s.2
    obtain ⟨c, hc⟩ := (hW v ((A.eQ v).symm ((A.spl v s).1))).2 (by rw [RingEquiv.apply_symm_apply]; exact hs.1)
    have : (fun a => (A.eQ v).symm ((A.spl v ((s • x) a)).1)) = c • (fun a => (A.eQ v).symm ((A.spl v (x a)).1)) := by
      funext a
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul, Prod.fst_mul, map_mul, Pi.smul_apply, Algebra.smul_def, hc]
    rw [this]
    exact Submodule.smul_mem _ c hx


set_option maxHeartbeats 400000 in
theorem lbAt_gen (A : LocAt F E n G) (hW : LocInt A)
    (hAlg : ∀ v (a : (A.pl v).1.adicCompletion F), A.spl v ((1 : E) ⊗ₜ[F] a) = (a, a))
    (Lb : Submodule (𝓞 E) (Fin n → E)) (hfr : FrAtB A Lb) (v : Fin G.P.nV) :
    Submodule.span (G.P.W v) ((fun x : Fin n → E => fun k => A.iw v (x k)) '' (Lb : Set (Fin n → E))) =
      colSpan (G.P.W v) ((bc (A.iw v) A.B : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) := by
  set fr : GL (Fin n) ((A.pl v).1.adicCompletion F) := bc (A.phE v) A.B with hfrdef
  have hM : ((bc (A.iw v) A.B : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) =
      (fr : Matrix (Fin n) (Fin n) _).map ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v) := by
    ext a b; rfl

  have h1 : ∀ t ∈ Submodule.span (G.P.W v) ((fun x : Fin n → E => fun k => A.iw v (x k)) '' (Lb : Set (Fin n → E))), IntB A v t := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      have hloc : (fun k => inclE (F := F) ((A.pl v).1.adicCompletion F) (y k)) ∈ Formalism.L2.Herm.locL (A.pl v).1 Lb :=
        Submodule.subset_span ⟨y, hy, rfl⟩
      have := (hfr v (fun k => A.eQ v (A.iw v (y k)))).1 ⟨_, hloc, fun a => by
        show (A.ph v) (inclE (F := F) ((A.pl v).1.adicCompletion F) (y a)) = A.eQ v ((A.eQ v).symm (A.phE v (y a)))
        rw [RingEquiv.apply_symm_apply]
        rfl⟩
      exact this
    | zero => exact intB_zero A v
    | add x y _ _ hx hy => exact intB_add A v x y hx hy
    | smul c x _ hx => exact intB_smul A hW v c x hx

  have h2 : ∀ t, IntB A v t → ∃ r : Fin n → G.P.W v,
      t = ((fr : Matrix (Fin n) (Fin n) _).map ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v)) *ᵥ
        (fun c => algebraMap (G.P.W v) (G.P.Qq v) (r c)) := by
    intro t ht
    choose r hr using fun c => (hW v ((A.eQ v).symm ((((fr⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
      (fun k => A.eQ v (t k))) c))).2 (by rw [RingEquiv.apply_symm_apply]; exact ht c)
    refine ⟨r, ?_⟩
    have e1 : (fun c => algebraMap (G.P.W v) (G.P.Qq v) (r c)) =
        fun c => (A.eQ v).symm ((((fr⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (fun k => A.eQ v (t k))) c) := by
      funext c; exact hr c
    rw [e1]
    funext i
    have e2 := RingHom.map_mulVec ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v) (fr : Matrix (Fin n) (Fin n) _)
      (((fr⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ (fun k => A.eQ v (t k))) i
    rw [mulVec_inv_mulVec] at e2
    exact (RingEquiv.symm_apply_apply (A.eQ v) (t i)).symm.trans e2

  have h3 : ∀ t, IntB A v t →
      t ∈ Submodule.span (G.P.W v) ((fun x : Fin n → E => fun k => A.iw v (x k)) '' (Lb : Set (Fin n → E))) := by
    intro t ht
    obtain ⟨x, hx, hxa⟩ := (hfr v (fun k => A.eQ v (t k))).2 ht
    have h4 := fst_mem_span A hW hAlg v Lb x hx
    have e3 : (fun a => (A.eQ v).symm ((A.spl v (x a)).1)) = t := by
      funext a; rw [hxa a]; exact RingEquiv.symm_apply_apply _ _
    rw [e3] at h4
    exact h4
  apply le_antisymm
  · intro t ht
    obtain ⟨r, rfl⟩ := h2 t (h1 t ht)
    rw [hM]
    exact mulVec_mem_colSpan _ r
  · unfold colSpan
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    apply h3
    intro a
    have hcol : (fun k => A.eQ v ((((bc (A.iw v) A.B : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v))) k c)) =
        fun k => (fr : Matrix (Fin n) (Fin n) _) k c := by
      funext k; rw [hM, Matrix.map_apply]; exact RingEquiv.apply_symm_apply _ _
    show ((((fr⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _)) *ᵥ
      (fun k => A.eQ v ((((bc (A.iw v) A.B : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v))) k c))) a ∈ _
    rw [hcol]
    have e4 : (((fr⁻¹ : GL (Fin n) ((A.pl v).1.adicCompletion F)) : Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) *ᵥ
        fun k => (fr : Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) k c) a =
        ((((fr⁻¹ : GL (Fin n) ((A.pl v).1.adicCompletion F)) : Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) *
          (fr : Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) : Matrix (Fin n) (Fin n) ((A.pl v).1.adicCompletion F)) a c) := by
      simp only [Matrix.mulVec, Matrix.mul_apply, dotProduct]
    rw [e4, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem frAtB_re [StarRing E] {r N : ℕ} (h : r = N) (A : LocAt F E N G) (Lb : Submodule (𝓞 E) (Fin r → E)) (B0 : GL (Fin r) E)
    (hB : A.B = Formalism.L2.Forms.reGL h E B0) (fr : ∀ v, GL (Fin r) ((A.pl v).1.adicCompletion F))
    (hfr0 : ∀ v (t : Fin r → (A.pl v).1.adicCompletion F),
      (∃ x ∈ Formalism.L2.Herm.locL (A.pl v).1 Lb, ∀ a, (A.spl v (x a)).1 = t a) ↔
        ∀ a, ((((fr v)⁻¹ : GL (Fin r) ((A.pl v).1.adicCompletion F)) :
          Matrix (Fin r) (Fin r) ((A.pl v).1.adicCompletion F)) *ᵥ t) a ∈ (A.pl v).1.adicCompletionIntegers F)
    (hrat : ∀ v, fr v = bc (A.phE v) B0) :
    FrAtB A (Lb.map (((reE (E := E) h : (Fin r → E) ≃ₗ[E] (Fin N → E)) : (Fin r → E) →ₗ[E] (Fin N → E)).restrictScalars (𝓞 E))) := by
  subst h
  rw [Formalism.MainNotions.G.KAat.map_reE_rfl]
  have hre : Formalism.L2.Forms.reGL (rfl : r = r) E B0 = B0 := by apply Units.ext; ext a b; rfl
  rw [hre] at hB
  intro v t
  rw [hB, ← hrat v]
  exact hfr0 v t

end Gen

section Of

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {p n : ℕ} {G : GAtP p}

theorem lbAtB_of (A : LocAt F E n G) (hW : LocInt A) (hAlg : SplAlg A)
    (Lb : Submodule (𝓞 E) (Fin n → E)) (hfr : FrAtB A Lb) : GlobalTheory.TwV.LbAtB A Lb := by
  intro v
  unfold GlobalTheory.TwV.locSp
  exact lbAt_gen A hW hAlg Lb hfr v

end Of

end GlobalTheory.TwV.LbB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitBoundStandardSeriesInertPlaces
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.OrbitBoundStdRec

theorem kvalGe_le {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 l : ℕ) [Fact l.Prime] (nu : Lt → YoungDiagram)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) {B B' : ℝ} (h : B' ≤ B) (H : product_zeroth_first_parts.KvalGe N0 N1 l nu Th B) :
    product_zeroth_first_parts.KvalGe N0 N1 l nu Th B' := fun I m =>
  (H I m).trans (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (Fact.out : l.Prime).one_lt.le) (neg_le_neg h))

theorem orbit_bound_rec : ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Ee : OrbitPlaces.Ent D), OrbitPlaces.Shape D L X Ee →
    (∀ u, ∀ i < D.R.m, ∀ t ∈ D.host.TT, Ee.row u i (false, t) 0 - Ee.row u i (false, t) 1 ≤ 2 * L.sc.a) → 5 ≤ K.dl1 → 4 ≤ K.dl2 →
    BeFam D Ee.ep Ee.be → (Ee.sg = fun _ _ => -1) → OrbitPlaces.OrbitBoundWithoutOperator Ee X K := by
  intro D L X K Ee hS hG hd1 hd2 hBe hsg
  intro w h hC0 hh hX u j hj t0 ht0 Th hB
  have hEv : HEv D (D.what₂.places.resChar w) := by
    have he := h.even
    unfold nP at he
    rw [if_neg (GlobalTheory.KerStd.WordFree.not_signal hC0)] at he
    exact he
  obtain ⟨hep, hbe⟩ := hBe w (Or.inl ⟨hC0, hEv⟩)
  have hs : Ee.sg w (false, t0) = -1 := by rw [hsg]
  rw [hs] at hB
  have z0 := _root_.GlobalTheory.KerZero.kvalGe_zero (OrbitPlaces.orbLoc Ee _ h u j (false, t0) Th) _ _ hep (hbe (false, t0)) hB
  have z1 := _root_.GlobalTheory.KerGaussA.kvalGe_gainA (OrbitPlaces.orbLoc Ee _ h u j (false, t0) Th) _ _ hep (hbe (false, t0)) hB
  have z2 := GlobalTheory.KerStd.WordFree.wordFreeNumber_le_orbitBound D L X K Ee hS hG hd1 hd2 _ h hC0 hh hX u j hj t0 ht0 Th
  rcases le_total (g0 X K (aL L) (bL L) (D.what₂.places.resChar w) (j + 1) t0) 0 with hm | hm
  · rw [max_eq_right hm]
    exact z0
  · rw [max_eq_left hm]
    exact kvalGe_le _ _ _ _ _ z2 z1

end GlobalTheory.OrbitBoundStdRec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothOfRelativeDimensionFibrePower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace GlobalTheory.FibPow

theorem smoothOfRelativeDimension_pow {X : Scheme.{0}} (A : Over X) (g : ℕ)
    (hA : SmoothOfRelativeDimension g A.hom) (k : ℕ) : SmoothOfRelativeDimension (k * g) (GlobalTheory.KS.pow A k).hom := by
  let e : GlobalTheory.KS.pow A k ≅ ReciprocityTheory.ChartRestriction.G.Out.powObj A k :=
    (limit.isLimit (Discrete.functor fun _ : Fin k => A)).conePointUniqueUpToIso
      (ReciprocityTheory.ChartRestriction.G.Out.powIsLimit A k)
  have hw : (GlobalTheory.KS.pow A k).hom = e.hom.left ≫ (ReciprocityTheory.ChartRestriction.G.Out.powObj A k).hom := (Over.w e.hom).symm
  have h1 := GlobalTheory.smoothOfRelativeDimension_powObj A g hA k
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have h2 : SmoothOfRelativeDimension (0 + k * g) (e.hom.left ≫ (ReciprocityTheory.ChartRestriction.G.Out.powObj A k).hom) :=
    inferInstance
  rw [hw]; simpa using h2

theorem smoothOfRelativeDimension_fibrePower : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (d g : ℕ),
    SmoothOfRelativeDimension d s → ∀ (A : Over X) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ k : ℕ, SmoothOfRelativeDimension (d + k * g) ((GlobalTheory.KS.pow A k).hom ≫ s) := by
  intro R _ X s d g hs A _ _ _ hA k
  have h := smoothOfRelativeDimension_pow A g hA k
  have h2 : SmoothOfRelativeDimension (k * g + d) ((GlobalTheory.KS.pow A k).hom ≫ s) := inferInstance
  rw [Nat.add_comm]; exact h2

end GlobalTheory.FibPow
end

