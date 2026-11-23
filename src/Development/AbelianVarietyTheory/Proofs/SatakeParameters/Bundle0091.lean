module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0088
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TransportFirstLevel
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SecondLevelOfNorm
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionRelation
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCoordField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitCoord

section General

variable {R T : Type} [CommRing R] [CommRing T] [Algebra R T]

theorem trace_mul_idem (hi : Function.Injective (algebraMap R T)) (c : T →+* T)
    (ht : ∀ z, algebraMap R T (Algebra.trace R T z) = z + c z) {e : T} (h1 : e * e = e) (h2 : e * c e = 0) (x y : T) :
    Algebra.trace R T (e * (x * y)) = Algebra.trace R T (e * x) * Algebra.trace R T (e * y) := by
  apply hi
  have hc : c e * c e = c e := by rw [← map_mul, h1]
  rw [RingHom.map_mul, ht, ht, ht]
  simp only [map_mul]
  linear_combination (-(x * y)) * h1 - (c x * c y) * hc - (x * c y + c x * y) * h2

theorem idem_mul_trace (c : T →+* T)
    (ht : ∀ z, algebraMap R T (Algebra.trace R T z) = z + c z) {e : T} (h1 : e * e = e) (h2 : e * c e = 0)
    {α : R} (h3 : e + c e = algebraMap R T α) (x : T) :
    e * algebraMap R T (α * Algebra.trace R T (e * x)) = e * x := by
  rw [map_mul, ht, ← h3, map_mul]
  linear_combination ((e + 1) * x) * h1 + (e * x + e * c x + c e * c x) * h2

theorem trace_idem_mul (hi : Function.Injective (algebraMap R T)) (c : T →+* T)
    (ht : ∀ z, algebraMap R T (Algebra.trace R T z) = z + c z) {e : T}
    {α : R} (h3 : e + c e = algebraMap R T α) (b : R) :
    Algebra.trace R T (e * algebraMap R T b) = b * α := by
  have : Algebra.trace R T e = α := hi (by rw [ht, h3])
  rw [mul_comm, ← Algebra.smul_def, map_smul, this, smul_eq_mul]

theorem exists_hom (hi : Function.Injective (algebraMap R T)) (c : T →+* T)
    (ht : ∀ z, algebraMap R T (Algebra.trace R T z) = z + c z) {e : T} (h1 : e * e = e) (h2 : e * c e = 0)
    {α : R} (h3 : e + c e = algebraMap R T α) {S K : Type} [CommRing S] [CommRing K] [Algebra S R] [Algebra S K]
    (φ : R →ₐ[S] K) (hα : φ α = 1) :
    ∃ π : T →+* K, ∀ x, π x = φ (Algebra.trace R T (e * x)) :=
  ⟨{ toFun := fun x => φ (Algebra.trace R T (e * x))
     map_one' := by
       have := trace_idem_mul hi c ht h3 1
       rw [RingHom.map_one, one_mul] at this
       rw [this, hα]
     map_mul' := fun x y => by rw [trace_mul_idem hi c ht h1 h2, map_mul]
     map_zero' := by rw [mul_zero, map_zero, map_zero]
     map_add' := fun x y => by rw [mul_add, map_add (f := _), map_add (f := _)] }, fun _ => rfl⟩

end General

section Single

variable {F : Type} [Field F] [NumberField F]

theorem evalV_single (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) : evalV F v (singleV F v a) = a := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v a

theorem evalV_single_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (a : Fv F v) : evalV F w (singleV F v a) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) a h

theorem single_evalV {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (h1 : evalV F v α = 1)
    (h2 : ∀ w, w ≠ v → evalV F w α = 0) (b : Af F) : singleV F v (evalV F v b) = α * b := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  change evalV F w (singleV F v (evalV F v b)) = evalV F w (α * b)
  by_cases hw : w = v
  · subst hw
    rw [evalV_single, map_mul, h1, one_mul]
  · rw [evalV_single_ne hw, map_mul, h2 w hw, zero_mul]

theorem single_mem {v : HeightOneSpectrum (𝓞 F)} {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F) :
    singleV F v a ∈ intAf F := by
  intro w
  by_cases hw : w = v
  · subst hw
    rw [evalV_single]; exact ha
  · rw [evalV_single_ne hw]; exact zero_mem _

end Single

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


variable (F E) in
def finT : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom


variable (F E) in
def intT : AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

theorem alg_inj (R : Type) [CommRing R] [Algebra F R] : Function.Injective (algebraMap R (R ⊗[F] E)) :=
  Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective

theorem finT_sig (σ : E →ₐ[F] E) (z : AF F ⊗[F] E) : finT F E (sigR (AF F) σ z) = sigR (Af F) σ (finT F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add a b ha hb => simp only [RingHom.map_add (f := _), ha, hb]
  | tmul a e => rfl

theorem finT_alg (a : AF F) : finT F E (algebraMap (AF F) _ a) = algebraMap (Af F) _ (sndA F a) := rfl

theorem mul_mem_intT {x y : Af F ⊗[F] E} (hx : x ∈ intT F E) (hy : y ∈ intT F E) : x * y ∈ intT F E := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intT F E) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem trace_mem (v : HeightOneSpectrum (𝓞 F)) {x : Af F ⊗[F] E} (hx : x ∈ intT F E) :
    evalV F v (Algebra.trace (Af F) (Af F ⊗[F] E) x) ∈ v.adicCompletionIntegers F := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, rfl⟩ := hx
    have h1 : a ⊗ₜ[F] (y : E) = a • ((1 : Af F) ⊗ₜ[F] (y : E)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h3 : Algebra.trace (Af F) (Af F ⊗[F] E) (a ⊗ₜ[F] (y : E)) = a * algebraMap F _ (Algebra.trace F E y) := by
      rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
        LinearMap.trace_baseChange, smul_eq_mul]
    rw [h3, map_mul, AlgHom.commutes]
    refine mul_mem (ha v) ?_
    have hi : IsIntegral ℤ (Algebra.trace F E y) := Algebra.isIntegral_trace y.isIntegral_coe
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v (⟨_, hi⟩ : 𝓞 F)
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [map_add (f := _), map_add (f := _)]; exact add_mem h1 h2
  | neg x _ h => rw [map_neg, map_neg]; exact neg_mem h

theorem exists_coord_field (hd : Module.finrank F E = 2) (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e)
    (hf : ∀ e, σ e = e → ∃ f, algebraMap F E f = e) (hI : ∀ z : Af F ⊗[F] E, z * z = z → z ∈ intT F E)
    (e : AF F ⊗[F] E) (h1 : e * e = e) (h2 : e * sigR (AF F) σ e = 0) (v : HeightOneSpectrum (𝓞 F)) (α : Af F)
    (hv : evalV F v α = 1) (hv' : ∀ w, w ≠ v → evalV F w α = 0)
    (h3 : e + sigR (AF F) σ e = algebraMap (AF F) _ (pairA F 0 α)) :
    ∃ (π : Af F ⊗[F] E →+* Fv F v) (s : Fv F v → AF F ⊗[F] E), (∀ x, s (π (finT F E x)) = e * x) ∧
      (∀ a, π (finT F E (s a)) = a) ∧ (∀ x, finT F E (s (π x)) = finT F E e * x) ∧
      (∀ x, finT F E e * x ∈ intT F E ↔ π x ∈ Formalism.UG.Ov F v) ∧
      ∀ x : F, π (finT F E (inclR (F := F) (AF F) (algebraMap F E x))) = algebraMap F (Fv F v) x := by
  have tA := GlobalTheory.FockCompare.SymplVal.trace_tensor hd σ hσ hf (AF F)
  have tf := GlobalTheory.FockCompare.SymplVal.trace_tensor hd σ hσ hf (Af F)
  have tt : ∀ z, Algebra.trace (Af F) (Af F ⊗[F] E) (finT F E z) = sndA F (Algebra.trace (AF F) _ z) := fun z => by
    apply alg_inj (F := F) (E := E)
    rw [tf, ← finT_alg, tA, RingHom.map_add (f := _), finT_sig]
  have g1 : finT F E e * finT F E e = finT F E e := by rw [← RingHom.map_mul, h1]
  have g2 : finT F E e * sigR (Af F) σ (finT F E e) = 0 := by
    rw [← finT_sig, ← RingHom.map_mul, h2, RingHom.map_zero]
  have g3 : finT F E e + sigR (Af F) σ (finT F E e) = algebraMap (Af F) _ α := by
    rw [← finT_sig, ← RingHom.map_add (f := _), h3]; rfl
  have k := fun b => trace_idem_mul (alg_inj _) _ tf g3 b
  obtain ⟨π, hπ⟩ := exists_hom (alg_inj _) _ tf g1 g2 g3 (evalV F v) hv
  have p3 : ∀ x, finT F E e * algebraMap (Af F) _ (singleV F v (π x)) = finT F E e * x := fun x => by
    rw [hπ, single_evalV hv hv']
    exact idem_mul_trace _ tf g1 g2 g3 x
  refine ⟨π, fun a => e * algebraMap (AF F) _ (pairA F 0 (singleV F v a)), fun x => ?_,
    fun a => ?_, fun x => ?_, fun x => ⟨fun h => ?_, fun h => ?_⟩, fun x => ?_⟩
  · refine Eq.trans ?_ (idem_mul_trace _ tA h1 h2 h3 x)
    beta_reduce
    rw [hπ, single_evalV hv hv', ← RingHom.map_mul, tt]
    congr 2
    exact Prod.ext (zero_mul _).symm rfl
  · rw [hπ, RingHom.map_mul, ← mul_assoc, g1, finT_alg, k, map_mul, hv, mul_one]
    exact evalV_single v a
  · rw [RingHom.map_mul, finT_alg]
    exact p3 x
  · rw [hπ]; exact trace_mem v h
  · rw [← p3]
    exact mul_mem_intT (hI _ g1) (AddSubgroup.subset_closure ⟨_, single_mem h, 1, rfl⟩)
  · have : finT F E (inclR (F := F) (AF F) (algebraMap F E x)) = algebraMap (Af F) _ (algebraMap F (Af F) x) := by
      change (sndA F 1) ⊗ₜ[F] (algebraMap F E x) = (algebraMap F (Af F) x) ⊗ₜ 1
      rw [map_one, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [this, hπ, k, map_mul, hv, mul_one, AlgHom.commutes]

end Field

theorem exists_coord : ∀ {D : D7} (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (π : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v) (s : Fv D.host.F v → Formalism.L2.Theta.AE D), (∀ x, s (π (finPart D x)) = e * x) ∧ (∀ a, π (finPart D (s a)) = a) ∧ (∀ x, finPart D (s (π x)) = finPart D e * x) ∧ (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) ∧ ∀ x : D.host.F, π (finPart D (incA D (algebraMap D.host.F D.host.E x))) = algebraMap D.host.F (Fv D.host.F v) x := by
  rintro D e ⟨h1, h2, v, ε, ⟨α, rfl, hv, hv'⟩, h3⟩
  exact ⟨v, exists_coord_field D.sp.cm.deg2 D.sp.cm.sig (fun e => star_star e) (fun e he => (D.sp.cm.fixed e).1 he)
    (GlobalTheory.AdIdem.idempotent_mem_intAE D) e h1 h2 v α hv hv' h3⟩

end GlobalTheory.SplitCoord

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsKummerFracCoboundaryFullGalois
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.NoLog

theorem exists_full_frac : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) [IsDomain P.R.B] (K : FinExt l) (b b' : P.R.B), b ≠ 0 →
    (∀ g ∈ GK K, b * P.actQ g b' - P.actQ g b * b' = b * P.actQ g b * ((kummer P g : ℚ_[l]) • P.tB)) →
    ∃ x y : P.R.B, x ≠ 0 ∧ ∀ g : GQ l, x * P.actQ g y - P.actQ g x * y = x * P.actQ g x * ((kummer P g : ℚ_[l]) • P.tB) := by
  intro l _ P _ K b b' hb h
  haveI := K.2
  haveI : Finite (GQ l ⧸ GK K) := Subgroup.quotient_finite_of_isOpen _ K.1.fixingSubgroup_isOpen
  haveI := Fintype.ofFinite (GQ l ⧸ GK K)
  let ι : P.R.B →+* FractionRing P.R.B := algebraMap P.R.B (FractionRing P.R.B)
  have hι : Function.Injective ι := IsFractionRing.injective P.R.B (FractionRing P.R.B)
  let e : GQ l → FractionRing P.R.B ≃+* FractionRing P.R.B := fun g =>
    IsFractionRing.ringEquivOfRingEquiv (A := P.R.B) (B := P.R.B) (P.actQ g).toRingEquiv
  have he : ∀ g z, e g (ι z) = ι (P.actQ g z) := fun g z =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _
  have hmul : ∀ s g z, e s (e g z) = e (s * g) z := by
    intro s g
    have : (e s).toRingHom.comp (e g).toRingHom = (e (s * g)).toRingHom := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors P.R.B)
      ext z
      show e s (e g (ι z)) = e (s * g) (ι z)
      rw [he, he, he, map_mul, AlgEquiv.mul_apply]
    intro z
    exact RingHom.congr_fun this z
  have hne : ∀ g (z : P.R.B), z ≠ 0 → ι (P.actQ g z) ≠ 0 := fun g z hz =>
    (map_ne_zero_iff ι hι).2 ((map_ne_zero_iff _ (P.actQ g).injective).2 hz)
  let T : GQ l → FractionRing P.R.B := fun g => ι ((kummer P g : ℚ_[l]) • P.tB)
  have hT : ∀ s g, e s (T g) = T (s * g) - T s := by
    intro s g
    simp only [T, he, map_smul, localPrime_galoisAction_periodT, kummer_mul, smul_smul, add_smul, map_add (f := _)]
    rw [mul_comm]; abel
  let f : FractionRing P.R.B := ι b' / ι b
  have hb0 : ι b ≠ 0 := (map_ne_zero_iff ι hι).2 hb
  have hf : ∀ g ∈ GK K, e g f - f = T g := by
    intro g hg
    have h1 := congrArg ι (h g hg)
    simp only [map_sub, map_mul] at h1
    have h2 := hne g b hb
    simp only [f, map_div₀, he]
    field_simp
    linear_combination h1
  let Fn : GQ l → FractionRing P.R.B := fun g => e g f - T g
  have h1 : ∀ s g, e s (Fn g) = Fn (s * g) + T s := by
    intro s g
    simp only [Fn, map_sub, hmul, hT]
    abel
  have h2 : ∀ g (k : ↥(GK K)), Fn (g * k) = Fn g := by
    intro g k
    have e1 : Fn k = f := by simp only [Fn, ← hf k k.2]; abel
    have := h1 g k
    rw [e1] at this
    simp only [Fn] at this ⊢
    linear_combination -this
  have h3 : ∀ g, Fn (QuotientGroup.mk g : GQ l ⧸ GK K).out = Fn g := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (GK K) g
    rw [hk, h2]
  have hnB : ((Fintype.card (GQ l ⧸ GK K) : ℕ) : P.R.B) ≠ 0 := by
    haveI := nontrivial_B P
    rw [← map_natCast (algebraMap ℚ_[l] P.R.B)]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℚ_[l] P.R.B)).2
      (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  have hn : ((Fintype.card (GQ l ⧸ GK K) : ℕ) : FractionRing P.R.B) ≠ 0 := by
    rw [← map_natCast ι]; exact (map_ne_zero_iff ι hι).2 hnB
  let fa : FractionRing P.R.B := ((Fintype.card (GQ l ⧸ GK K) : ℕ) : FractionRing P.R.B)⁻¹ * ∑ q : GQ l ⧸ GK K, Fn q.out
  have hfa : ∀ s, e s fa - fa = T s := by
    intro s
    have h4 : ∑ q : GQ l ⧸ GK K, Fn (s * q.out) = ∑ q : GQ l ⧸ GK K, Fn q.out :=
      Fintype.sum_equiv (MulAction.toPerm s) _ _ fun q => by
        rw [MulAction.toPerm_apply, ← MulAction.Quotient.mk_smul_out, h3, smul_eq_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [fa, map_mul, map_inv₀, map_natCast, map_sum, h1]
    rw [Finset.sum_add_distrib, h4, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  obtain ⟨y, x, hx, hxy⟩ := IsFractionRing.div_surjective (A := P.R.B) fa
  have hx0 : x ≠ 0 := nonZeroDivisors.ne_zero hx
  refine ⟨x, y, hx0, fun g => ?_⟩
  have hxy' : ι y / ι x = fa := hxy
  have k := hfa g
  rw [← hxy', map_div₀, he, he] at k
  have k1 := hne g x hx0
  have k2 : ι x ≠ 0 := (map_ne_zero_iff ι hι).2 hx0
  apply hι
  simp only [map_sub, map_mul]
  field_simp at k
  linear_combination k

end GlobalTheory.Pst.NoLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLogOnePlusKerThetaDeRhamPlus
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.Pst.LogExist

variable {l : ℕ} [Fact l.Prime]

def logSum (w : Per.AinfP l) (n : ℕ) : Per.AinfP l :=
  ∑ k ∈ Finset.range n, (-1) ^ k * Ring.inverse (((k + 1 : ℕ) : Per.AinfP l)) * w ^ (k + 1)

theorem logSum_succ (w : Per.AinfP l) (n : ℕ) :
    logSum w (n + 1) = logSum w n + (-1) ^ n * Ring.inverse (((n + 1 : ℕ) : Per.AinfP l)) * w ^ (n + 1) := by
  simp only [logSum, Finset.sum_range_succ]

theorem logSum_cauchy {w : Per.AinfP l} (hw : w ∈ Per.kerP l) (n : ℕ) :
    logSum w n ≡ logSum w (n + 1) [SMOD (Per.kerP l ^ n • ⊤ : Submodule (Per.AinfP l) (Per.AinfP l))] := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, logSum_succ, sub_add_cancel_left]
  refine (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_left _ _ ?_)
  exact Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.pow_mem_pow hw _)

def logP {w : Per.AinfP l} (hw : w ∈ Per.kerP l) : Per.BdRp l :=
  (GlobalTheory.RingIface.exists_bdRp_equiv l).choose.symm (AdicCompletion.mk (Per.kerP l) (Per.AinfP l)
    (AdicCompletion.AdicCauchySequence.mk (Per.kerP l) (Per.AinfP l) (logSum w) (logSum_cauchy hw)))

theorem ev_logP {w : Per.AinfP l} (hw : w ∈ Per.kerP l) (n : ℕ) :
    Per.ev l n (logP hw) = Ideal.Quotient.mk _ (logSum w n) := by
  rw [← (GlobalTheory.RingIface.exists_bdRp_equiv l).choose_spec.2, logP, RingEquiv.apply_symm_apply, AdicCompletion.evalₐ_mk]
  rfl

theorem factorial_mul_logSum (w : Per.AinfP l) (n : ℕ) :
    ((n.factorial : ℕ) : Per.AinfP l) * logSum w n =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * w ^ (k + 1) := by
  rw [logSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k + 1 ≤ n := Finset.mem_range.1 hk
  have hd : n.factorial / (k + 1) * (k + 1) = n.factorial :=
    Nat.div_mul_cancel (Nat.dvd_factorial (Nat.succ_pos k) hkn)
  have hu : ((k + 1 : ℕ) : Per.AinfP l) * Ring.inverse (((k + 1 : ℕ) : Per.AinfP l)) = 1 :=
    Ring.mul_inverse_cancel _ (GlobalTheory.RingBasics.isUnit_nat l _ (Nat.succ_ne_zero k))
  have hc : ((n.factorial : ℕ) : Per.AinfP l) = ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * ((k + 1 : ℕ) : Per.AinfP l) := by
    rw [← Nat.cast_mul, hd]
  rw [hc]
  linear_combination (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * w ^ (k + 1) * hu

theorem isLogP_logP {w : Per.AinfP l} (hw : w ∈ Per.kerP l) : IsLogP w (logP hw) := by
  intro n
  rw [ev_logP, ← factorial_mul_logSum, map_mul, map_natCast]

theorem exists_isLogP : ∀ (l : ℕ) [Fact l.Prime] (w : Per.AinfP l), w ∈ Per.kerP l → ∃ u : Per.BdRp l, IsLogP w u :=
  fun _ _ _ hw => ⟨logP hw, isLogP_logP hw⟩

end GlobalTheory.Pst.LogExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfInertPrimeEllipticCurveLocalData
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem BeData.exists_of_curveData : ∀ (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → ∀ (d : ℕ) [NeZero d], Even d →
    ∃ (om oms : Fin (d / 2) → MaximalUnramifiedExtension p) (ζ : MaximalUnramifiedExtension p), BeData p d σ F (cob F (phFF p g2 g3 s2 ε)) om oms ζ := by
  intro p _ g2 g3 s2 ε σ F hC d _ hd
  obtain ⟨-, hg2, hg3, hε, hth, hσ, hF, hN⟩ := hC
  have hff := Formalism.L2.Th1.D.FAux.ffs (l := p) Formalism.L2.Th1.D.first_level_on_curve g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN
  have hp : p.Prime := Fact.out
  have hd0 : d ≠ 0 := NeZero.ne d
  have h1 : 1 < p ^ d := Nat.one_lt_pow hd0 hp.one_lt
  obtain ⟨ζ, hζ⟩ := Formalism.L2.Th1.D.kurRoots p (p ^ d - 1) (by omega) (fun hdv => by
    have h2 : p ∣ p ^ d := dvd_pow_self p hd0
    have h3 : p ∣ 1 := by
      have := Nat.dvd_sub h2 hdv
      rwa [Nat.sub_sub_self h1.le] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 h3))
  obtain ⟨om, oms, hO, hT⟩ := Formalism.L2.Th1.D.trDualExists (MaximalUnramifiedExtension p) p d σ hσ hd ζ hζ
  exact ⟨om, oms, ζ, hσ, hF, hff.1, hff.2.1, hO, hT, hζ⟩

end GlobalTheory.KerStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisLogTeichmullerRatioEqAddKummer
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

variable {l : ℕ} [Fact l.Prime]

theorem map_linv (f : Per.AinfP l →+* Per.AinfP l) : f (linv l) = linv l := by
  have h := congrArg f (mul_linv (l := l))
  rw [map_mul, map_natCast, map_one] at h
  have h2 := mul_linv (l := l)
  linear_combination (linv l) * h - f (linv l) * h2

theorem beta_mem_kerP (ϖ : Per.Fl l) (hu : ϖ.untilt = ((l : ℕ) : Per.OC l)) : beta ϖ ∈ Per.kerP l := by
  rw [← ThetaD.fontaineTheta_eq_zero]
  have h := congrArg (Per.θP l) (l_mul_beta ϖ)
  rw [map_mul, map_sub, map_natCast, ThetaD.fontaineTheta_algebraMap₂, WittVector.fontaineTheta_teichmuller, hu] at h
  have hl : ((l : ℕ) : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  refine (mul_eq_zero.1 (h.trans ?_)).resolve_left hl
  simp

theorem gal_beta (g : GQ l) (ϖ e : Per.Fl l) (h : Per.σF g ϖ = ϖ * e) :
    Per.extP (Per.σA g) (beta ϖ) = beta ϖ + algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.mu e) +
      beta ϖ * algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.mu e) := by
  have e1 : Per.σA g (Per.tm ϖ) = Per.tm ϖ * Per.tm e := by
    have h1 := gal_quot g ϖ e h 1
    simp only [map_one, mul_one, map_sub] at h1
    exact sub_left_injective h1
  rw [beta, map_sub, map_mul, map_one, map_linv, GlobalTheory.RingBasics.awayMap_algebraMap₂, e1, map_mul]
  simp only [GlobalTheory.MemLoc.mu, map_sub, map_one]
  ring

theorem isLogP_map {e : Per.Fl l} (he : e.untilt = 1) {t : Per.Acris l} (ht : IsLogA e t)
    {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) :
    IsLogP (algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.mu e)) (j t) := by
  intro n
  have hu : ∀ k : ℕ, ∃ u : Per.AinfP l, ((k + 1 : ℕ) : Per.AinfP l) * u = 1 := fun k =>
    (GlobalTheory.RingBasics.isUnit_nat l _ k.succ_ne_zero).exists_right_inv
  choose u hu using hu
  have hf : ∀ k : ℕ, IsUnit ((k.factorial : ℕ) : Per.AinfP l) := fun k =>
    GlobalTheory.RingBasics.isUnit_nat l _ k.factorial_ne_zero
  obtain ⟨d, hd⟩ := (hf n).exists_right_inv
  obtain ⟨c, hc⟩ : ∃ c : Per.AinfP l, ((n.factorial : ℕ) : Per.AinfP l) * c =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.mu e)) ^ (k + 1) :=
    ⟨d * _, by rw [← mul_assoc, hd, one_mul]⟩
  have key := (_root_.GlobalTheory.MemLoc.crisP_unique_equivariant l j hj).2.2 n t (algebraMap (Per.AinfP l) (Per.BdRp l) c) (by
    intro r
    obtain ⟨N, hN⟩ := ht r
    obtain ⟨s, hs, z, hz⟩ := hN (max N n) (le_max_left _ _)
    refine ⟨s, z, 0, by rw [← hz]; ring, ?_⟩
    rw [map_zero, mul_zero, map_zero, ← map_sub, LogFun.ev_alg, Ideal.Quotient.eq_zero_iff_mem,
      LogFun.partial_eq u hu _ _ _ (hf _) hs, LogFun.partial_eq u hu _ _ _ (hf _) hc, ← neg_sub]
    exact neg_mem (LogFun.partial_sub_mem _ u _ (LogFun.mu_mem he) (le_max_right _ _)))
  rw [key, LogFun.ev_alg, ← map_natCast (Ideal.Quotient.mk (Per.kerP l ^ n)), ← map_mul, hc]

theorem gal_log : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (Co : Core l), Co.ζ = P.ζQ → ∀ ϖ : Per.Fl l,
  (∀ m : ℕ, (rootT ϖ m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (lRoot l m)) → ϖ.untilt = ((l : ℕ) : Per.OC l) →
  ∀ u : Per.BdRp l, IsLogP (beta ϖ) u → ∀ g : GQ l,
    Per.σDp g u = u + Co.j (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (kummer P g)) * Co.t) := by
  intro l _ P Co hζ ϖ hr hu u hlog g
  have hd : ∀ m, g (lRoot l m) = Co.ζ m ^ (PadicInt.toZModPow m (kummer P g)).val * lRoot l m := fun m => by
    rw [hζ]; exact isKummer_kummer P g m
  have hd' : ∀ m, g (lRoot l m) / lRoot l m = Co.ζ m ^ (PadicInt.toZModPow m (kummer P g)).val := fun m => by
    rw [hd, mul_div_cancel_right₀ _ (lRoot_ne_zero l m)]
  obtain ⟨e, he⟩ := exists_tilt (fun m => Co.ζ m ^ (PadicInt.toZModPow m (kummer P g)).val)
    (fun m => by rw [← hd', ← hd', div_pow, ← map_pow, lRoot_succ]) 1 (by simp [Co.ζ_zero])
  have he1 : e.untilt = 1 := Subtype.ext (by
    have := he 0
    rw [Co.ζ_zero, one_pow, map_one] at this
    exact this)
  have hxe : Per.σF g ϖ = ϖ * e := gal_eq_mul g ϖ e fun m => by
    rw [hr, he, ← map_mul, mul_comm, ← hd]
    exact GlobalTheory.RingBasics.σC_coe g _
  obtain ⟨y, -, hy, -⟩ := exists_isLogA l e he1
  rw [← log_eq Co e (kummer P g) y he hy]
  refine IsLogP.add (beta_mem_kerP ϖ hu) (LogFun.mu_mem he1) hlog (isLogP_map he1 hy Co.j_cris) ?_
  have h := IsLogP.gal hlog g
  rwa [gal_beta g ϖ e hxe] at h

end GlobalTheory.Pst.StLat
end

