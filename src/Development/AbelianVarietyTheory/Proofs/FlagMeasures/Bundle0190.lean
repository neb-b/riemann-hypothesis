module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0002
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Formalism.FormalDegreeBessel.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0184

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFlagIsotropicSelfDual
section
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

noncomputable section

namespace GlobalTheory.FlagIso

theorem exists_extension {O K V : Type} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (Λ P : Submodule O V) (hfg : Λ.FG) (hspan : Submodule.span K (Λ : Set V) = ⊤)
    (hsat : ∀ c : O, c ≠ 0 → ∀ v ∈ Λ, c • v ∈ P → v ∈ P) (f : V →ₗ[K] K)
    (hf : ∀ z ∈ P, f z ∈ (algebraMap O K).range) :
    ∃ g : V →ₗ[K] K, (∀ z ∈ Λ, g z ∈ (algebraMap O K).range) ∧ ∀ z ∈ Λ, z ∈ P → g z = f z := by
  have hloc : IsLocalizedModule (nonZeroDivisors O) Λ.subtype :=
    { map_units := fun s => by
        have := isLocalizedModule_id (nonZeroDivisors O) V K
        exact IsLocalizedModule.map_units (S := nonZeroDivisors O) (LinearMap.id : V →ₗ[O] V) s
      surj := fun y => by
        have hy : y ∈ Submodule.span K (Λ : Set V) := by rw [hspan]; trivial
        obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) K (Λ : Set V) y hy
        rw [Submodule.span_eq] at hs
        exact ⟨(⟨_, hs⟩, s), rfl⟩
      exists_of_eq := fun h => ⟨1, by rw [Subtype.ext h]⟩ }
  have : Module.Finite O Λ := Module.Finite.iff_fg.2 hfg
  let Q : Submodule O Λ := P.comap Λ.subtype
  have : Module.Flat O (Λ ⧸ Q) := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨v, rfl⟩ := Q.mkQ_surjective q
    obtain ⟨c, hc⟩ := hq
    have h1 : Q.mkQ ((c : O) • v) = 0 := by rw [map_smul]; exact hc
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hsat c (nonZeroDivisors.coe_ne_zero c) v v.2 h1
  have : Module.FinitePresentation O (Λ ⧸ Q) := Module.finitePresentation_of_finite _ _
  have : Module.Projective O (Λ ⧸ Q) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property Q.mkQ LinearMap.id Q.mkQ_surjective
  let π : Λ →ₗ[O] Λ := LinearMap.id - s ∘ₗ Q.mkQ
  have hπ : ∀ v, π v ∈ Q := by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have h1 : Q.mkQ (s (Q.mkQ v)) = Q.mkQ v := LinearMap.congr_fun hs _
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1, sub_self]
  have hπ' : ∀ v ∈ Q, π v = v := by
    intro v hv
    have h1 : Q.mkQ v = 0 := by rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h1, map_zero, sub_zero]
  have hu : ∀ x : nonZeroDivisors O, IsUnit (algebraMap O (Module.End O K) x) :=
    fun x => IsLocalizedModule.map_units (S := nonZeroDivisors O) (Algebra.linearMap O K) x
  let g : V →ₗ[K] K := LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) K
      (IsLocalizedModule.lift (nonZeroDivisors O) Λ.subtype
        (f.restrictScalars O ∘ₗ Λ.subtype ∘ₗ π) hu)
  have hg : ∀ y : Λ, g y = f (π y) := fun y =>
    IsLocalizedModule.lift_apply (nonZeroDivisors O) Λ.subtype _ hu y
  refine ⟨g, fun z hz => ?_, fun z hz hP => ?_⟩
  · rw [hg ⟨z, hz⟩]
    exact hf _ (hπ _)
  · rw [hg ⟨z, hz⟩, hπ' ⟨z, hz⟩ hP]

section Form

variable {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def hR (x : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun y := Formalism.UG.hform (starRingEnd E) J x y
  map_add' y z := by simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hR_apply (x y : Fin n → E) : hR J x y = Formalism.UG.hform (starRingEnd E) J x y := rfl

theorem hform_star (hJ : Formalism.UG.IsHerm (starRingEnd E) J) (x y : Fin n → E) :
    star (Formalism.UG.hform (starRingEnd E) J x y) = Formalism.UG.hform (starRingEnd E) J y x := by
  have h : ∀ i j, star (J i j) = J j i := fun i j => by
    have := congrFun (congrFun hJ j) i
    exact this
  simp only [Formalism.UG.hform, star_sum, star_mul', starRingEnd_apply, star_star, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem exists_hR_eq (hJ : J.det ≠ 0) (g : (Fin n → E) →ₗ[E] E) : ∃ y, hR J y = g := by
  refine ⟨star ((fun j => g (Pi.single j 1)) ᵥ* J⁻¹), ?_⟩
  ext j
  have h1 : ((fun j => g (Pi.single j 1)) ᵥ* J⁻¹) ᵥ* J = fun j => g (Pi.single j 1) := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (Ne.isUnit hJ), Matrix.vecMul_one]
  have h2 := congrFun h1 j
  simp only [LinearMap.comp_apply, LinearMap.single_apply, hR_apply]
  rw [← h2]
  simp only [Formalism.UG.hform, starRingEnd_apply, Pi.star_apply, star_star]
  simp [Pi.single_apply, Matrix.vecMul, dotProduct]

end Form

theorem star_mem_range {E : Type} [Field E] [StarRing E] {a : E}
    (h : a ∈ (algebraMap (𝓞 E) E).range) : star a ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨b, rfl⟩ := h
  exact ⟨⟨_, map_isIntegral_int (starRingEnd E) b.isIntegral_coe⟩, rfl⟩

theorem card_le_of_isotropic {n k : ℕ} (ε : Fin n → Bool) (u : Fin k → Fin n → ℂ)
    (hu : LinearIndependent ℂ u) (hiso : ∀ i j, star (u i) ⬝ᵥ (Jm ε *ᵥ u j) = 0) (b : Bool) :
    k ≤ (univ.filter fun a => ε a = b).card := by
  let T : (Fin k → ℂ) →ₗ[ℂ] ({a // ε a = b} → ℂ) :=
    LinearMap.funLeft ℂ ℂ Subtype.val ∘ₗ Fintype.linearCombination ℂ u
  have hT : Function.Injective T := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    have h0 : star (∑ i, c i • u i) ⬝ᵥ (Jm ε *ᵥ ∑ i, c i • u i) = 0 := by
      simp only [star_sum, star_smul, sum_dotProduct, Matrix.mulVec_sum, dotProduct_sum, Matrix.mulVec_smul,
        smul_dotProduct, dotProduct_smul, hiso, smul_zero, Finset.sum_const_zero]
    have h1 : ∀ a, ε a = b → (∑ i, c i • u i) a = 0 := fun a ha => congrFun hc ⟨a, ha⟩
    have h3 : ∑ i, c i • u i = 0 := by
      generalize ∑ i, c i • u i = w at h0 h1
      have h2 : star w ⬝ᵥ (Jm ε *ᵥ w) = (if b then -1 else 1) * (star w ⬝ᵥ w) := by
        simp only [dotProduct, Jm, Matrix.mulVec_diagonal, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases ha : ε a = b
        · simp [h1 a ha]
        · cases b <;> simp_all
      rw [h2] at h0
      have h4 : star w ⬝ᵥ w = 0 := by cases b <;> simpa using h0
      open ComplexOrder in exact dotProduct_star_self_eq_zero.1 h4
    funext i
    exact Fintype.linearIndependent_iff.1 hu c h3 i
  have := LinearMap.finrank_le_finrank_of_injective hT
  simpa [Fintype.card_subtype] using this

variable (I : AutInst)

theorem rkK_le_rkR (S : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (hS : ∀ y ∈ S, ∀ z ∈ S, Formalism.UG.hform (starRingEnd I.E) I.J y z = 0) (v : InfinitePlace I.F) :
    rkK S ≤ rkR (I.ε v) := by
  obtain ⟨b, hbS, -, hb⟩ := Submodule.exists_fun_fin_finrank_span_eq I.E (S : Set (Fin I.n → I.E))
  letI : Algebra I.E ℂ := (I.φ v).toAlgebra
  have h1 : LinearIndependent ℂ (fun i => (I.φ v) ∘ b i) :=
    (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 hb
  have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hPi : ∀ w : Fin I.n → ℂ, I.P v *ᵥ ((I.P v)⁻¹ *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec]
  have h2 : LinearIndependent ℂ (fun i => (I.P v)⁻¹ *ᵥ ((I.φ v) ∘ b i)) := by
    apply LinearIndependent.of_comp (Matrix.mulVecLin (I.P v))
    simpa [Function.comp_def, hPi] using h1
  have h3 : ∀ i j, star ((I.P v)⁻¹ *ᵥ ((I.φ v) ∘ b i)) ⬝ᵥ
      (Jm (I.ε v) *ᵥ ((I.P v)⁻¹ *ᵥ ((I.φ v) ∘ b j))) = 0 := by
    intro i j
    rw [← I.P_spec v, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPi, Matrix.dotProduct_mulVec,
      ← Matrix.star_mulVec, hPi]
    have h4 := congrArg (I.φ v) (hS _ (hbS i) _ (hbS j))
    rw [map_zero] at h4
    rw [← h4]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.UG.hform, map_sum, map_mul, starRingEnd_apply, I.cm.cmUnram.2.1, dotProduct,
      Matrix.mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply, Function.comp_apply, Matrix.map_apply]
  exact le_min (card_le_of_isotropic _ _ h2 h3 true) (card_le_of_isotropic _ _ h2 h3 false)

theorem mem_perpIn (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) (y : Fin I.n → I.E) :
    y ∈ perpIn I x S ↔ y ∈ lamX I x ∧ ∀ s ∈ S, Formalism.UG.hform (starRingEnd I.E) I.J s y = 0 := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => exact ⟨zero_mem _, fun s _ => map_zero (hR I.J s)⟩
  | add y z _ _ hy hz =>
    exact ⟨add_mem hy.1 hz.1, fun s hs => by
      rw [← hR_apply, map_add (f := _), hR_apply, hR_apply, hy.2 s hs, hz.2 s hs, add_zero]⟩
  | smul c y _ hy =>
    exact ⟨Submodule.smul_mem _ _ hy.1, fun s hs => by
      rw [← hR_apply, LinearMap.map_smul_of_tower, hR_apply, hy.2 s hs, smul_zero]⟩

theorem hform_span (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) {y s : Fin I.n → I.E}
    (hy : y ∈ Submodule.span I.E (perpIn I x S : Set (Fin I.n → I.E))) (hs : s ∈ S) :
    Formalism.UG.hform (starRingEnd I.E) I.J s y = 0 := by
  have : Submodule.span I.E (perpIn I x S : Set (Fin I.n → I.E)) ≤ LinearMap.ker (hR I.J s) :=
    Submodule.span_le.2 fun z hz => ((mem_perpIn I x S z).1 hz).2 s hs
  exact this hy

theorem flag_isotropic : ∀ (I : AutInst) (x : I.GA), (∀ y ∈ stepLt I x (1 / 2), ∀ z ∈ stepLt I x (1 / 2), Formalism.UG.hform (starRingEnd I.E) I.J y z = 0) ∧ (∀ v, rkK (stepLt I x (1 / 2)) ≤ rkR (I.ε v)) ∧ ∀ R : Submodule (𝓞 I.E) (Fin I.n → I.E), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≤ perpIn I x R → ∀ y ∈ Submodule.span I.E (perpIn I x R : Set (Fin I.n → I.E)), (∀ z ∈ perpIn I x R, Formalism.UG.hform (starRingEnd I.E) I.J z y ∈ (algebraMap (𝓞 I.E) I.E).range) → ∃ y' ∈ perpIn I x R, y - y' ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)) := by
  intro I x
  obtain ⟨-, -, hd1, hd2⟩ := _root_.GlobalTheory.Count.PerpStep.main I x
  obtain ⟨-, hfg, hspan, hdual, -⟩ := GlobalTheory.T.autPointLatticeIntersection_selfDual_properties I x
  have hiso : ∀ y ∈ stepLt I x (1 / 2), ∀ z ∈ stepLt I x (1 / 2),
      Formalism.UG.hform (starRingEnd I.E) I.J y z = 0 := by
    intro y hy z hz
    obtain ⟨-, -, h1, h2, -⟩ := _root_.GlobalTheory.CountSteps.steps I x (1 / 2) (by norm_num)
    obtain ⟨-, -, h3, -⟩ := _root_.GlobalTheory.CountSteps.steps I x (1 / 2)⁻¹ (by norm_num)
    have h4 := h3 (h2 (1 / 2)⁻¹ (by norm_num) (h1 hz))
    rw [← (hd1 (1 / 2) (by norm_num)).2] at h4
    exact ((mem_perpIn I x _ z).1 h4).2 y hy
  refine ⟨hiso, rkK_le_rkR I _ hiso, fun R hR hRR y hy hint => ?_⟩
  obtain ⟨-, -, hpp, -⟩ := hd2 R R hR hR le_rfl
  obtain ⟨g, hg, hgf⟩ := exists_extension (lamX I x) (perpIn I x R) hfg hspan
    (fun c hc v hv h => by
      refine (mem_perpIn I x R v).2 ⟨hv, fun s hs => ?_⟩
      have h1 := ((mem_perpIn I x R _).1 h).2 s hs
      rw [← hR_apply, LinearMap.map_smul_of_tower] at h1
      exact (smul_eq_zero.1 h1).resolve_left hc)
    (FlagIso.hR I.J y) (fun z hz => by
      rw [hR_apply, ← hform_star _ I.J_herm]
      exact star_mem_range (hint z hz))
  obtain ⟨y', rfl⟩ := exists_hR_eq I.J I.J_det g
  have hy' : y' ∈ lamX I x := (hdual y').2 fun z hz => by
    rw [← hform_star _ I.J_herm]
    exact star_mem_range (hg z hz)
  have heq : ∀ z ∈ perpIn I x R, Formalism.UG.hform (starRingEnd I.E) I.J z y' =
      Formalism.UG.hform (starRingEnd I.E) I.J z y := fun z hz => by
    rw [← hform_star _ I.J_herm, ← hform_star _ I.J_herm y]
    exact congrArg star (hgf z ((mem_perpIn I x R z).1 hz).1 hz)
  refine ⟨y', (mem_perpIn I x R y').2 ⟨hy', fun s hs => ?_⟩, ?_⟩
  · rw [heq s (hRR hs)]
    exact hform_span I x R hy hs
  · have h1 : y - y' ∈ Submodule.span I.E (lamX I x : Set (Fin I.n → I.E)) := by rw [hspan]; trivial
    obtain ⟨c, hc⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 I.E)) I.E _ _ h1
    rw [Submodule.span_eq] at hc
    have hc' : (c : 𝓞 I.E) • (y - y') ∈ lamX I x := hc
    have h2 : (c : 𝓞 I.E) • (y - y') ∈ R := by
      rw [← hpp]
      refine (mem_perpIn I x _ _).2 ⟨hc', fun s hs => ?_⟩
      rw [← hR_apply, LinearMap.map_smul_of_tower, map_sub, hR_apply, hR_apply, heq s hs, sub_self, smul_zero]
    have hc0 : algebraMap (𝓞 I.E) I.E c ≠ 0 := by
      simpa using nonZeroDivisors.coe_ne_zero c
    have h3 := Submodule.smul_mem (Submodule.span I.E (R : Set (Fin I.n → I.E)))
      (algebraMap (𝓞 I.E) I.E c)⁻¹ (Submodule.subset_span h2)
    rwa [← algebraMap_smul I.E (c : 𝓞 I.E), smul_smul, inv_mul_cancel₀ hc0, one_smul] at h3

end GlobalTheory.FlagIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellPointBlockEndsLeadingMinors
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.PtMinor

noncomputable def minor (bs : List (ℂ × ℕ)) (m : ℕ) : ℂ := (Matrix.of fun a b : Fin m => ptEntry bs a b).det

def ends (c : ℕ) (bs : List (ℂ × ℕ)) : List ℕ := ((bs.map Prod.snd).scanl (· + ·) c).tail

theorem ends_nil (c : ℕ) : ends c [] = [] := by simp [ends]

theorem ends_cons (c : ℕ) (t : ℂ) (s : ℕ) (bs : List (ℂ × ℕ)) :
    ends c ((t, s) :: bs) = (c + s) :: ends (c + s) bs := by
  cases bs <;> simp [ends]

theorem det_anti (t : ℂ) (ht : t ≠ 0) (s : ℕ) :
    (Matrix.of fun a b : Fin s => if a.val + b.val + 1 = s then t else 0).det ≠ 0 := by
  have : (Matrix.of fun a b : Fin s => if a.val + b.val + 1 = s then t else 0) =
      (Matrix.diagonal fun _ : Fin s => t).submatrix (Fin.revPerm : Equiv.Perm (Fin s)) id := by
    ext a b
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.diagonal_apply, Fin.revPerm_apply, id, Fin.ext_iff,
      Fin.val_rev]
    have := a.2
    exact if_congr (by omega) rfl rfl
  rw [this, Matrix.det_permute]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s))) with h | h <;> simp [h, ht]

theorem minor_cons (t : ℂ) (s : ℕ) (bs : List (ℂ × ℕ)) (m : ℕ) :
    minor ((t, s) :: bs) (s + m) =
      (Matrix.of fun a b : Fin s => if a.val + b.val + 1 = s then t else 0).det * minor bs m := by
  unfold minor
  rw [← Matrix.det_fromBlocks_zero₂₁ _ (0 : Matrix (Fin s) (Fin m) ℂ),
    ← Matrix.det_submatrix_equiv_self finSumFinEquiv]
  congr 1
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [ptEntry]

theorem minor_lt (t : ℂ) (s : ℕ) (bs : List (ℂ × ℕ)) (m : ℕ) (h1 : 1 ≤ m) (h2 : m < s) :
    minor ((t, s) :: bs) m = 0 := by
  unfold minor
  refine Matrix.det_eq_zero_of_row_eq_zero ⟨0, h1⟩ fun j => ?_
  have := j.2
  simp only [Matrix.of_apply, ptEntry]
  split_ifs <;> first | rfl | omega

theorem ends_bd (bs : List (ℂ × ℕ)) (h : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) (c : ℕ) :
    (∀ x ∈ ends c bs, c < x ∧ x ≤ c + (bs.map Prod.snd).sum) ∧ (ends c bs).Nodup ∧
      (bs ≠ [] → c + (bs.map Prod.snd).sum ∈ ends c bs) := by
  induction bs generalizing c with
  | nil => simp [ends_nil]
  | cons p bs ih =>
    obtain ⟨t, s⟩ := p
    have hs : 1 ≤ s := (h (t, s) (by simp)).2
    obtain ⟨i1, i2, i3⟩ := ih (fun b hb => h b (by simp [hb])) (c + s)
    rw [ends_cons]
    simp only [List.map_cons, List.sum_cons, List.mem_cons, List.nodup_cons]
    refine ⟨?_, ⟨fun hm => ?_, i2⟩, fun _ => ?_⟩
    · rintro x (rfl | hx)
      · omega
      · have := i1 x hx
        omega
    · have := i1 _ hm
      omega
    · by_cases hb : bs = []
      · subst hb; simp
      · right
        rw [← add_assoc]
        exact i3 hb

theorem minor_ne_iff (bs : List (ℂ × ℕ)) (h : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) (c l : ℕ) (hl : 1 ≤ l) :
    minor bs l ≠ 0 ↔ c + l ∈ ends c bs := by
  induction bs generalizing c l with
  | nil =>
    have : minor [] l = 0 := Matrix.det_eq_zero_of_row_eq_zero ⟨0, hl⟩ fun j => by simp [ptEntry]
    simp [this, ends_nil]
  | cons p bs ih =>
    obtain ⟨t, s⟩ := p
    have ht : t ≠ 0 := (h (t, s) (by simp)).1
    have h' : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2 := fun b hb => h b (by simp [hb])
    have hb := (ends_bd bs h' (c + s)).1
    rw [ends_cons, List.mem_cons]
    rcases lt_or_ge l s with hls | hls
    · rw [minor_lt t s bs l hl hls]
      refine ⟨fun h0 => absurd rfl h0, ?_⟩
      rintro (h1 | h1)
      · omega
      · have := hb _ h1
        omega
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hls
      rw [minor_cons, mul_ne_zero_iff, and_iff_right (det_anti t ht s)]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [minor]
      · rw [ih h' (c + s) m hm, add_assoc]
        refine ⟨Or.inr, ?_⟩
        rintro (h1 | h1)
        · omega
        · exact h1

theorem one_le_max_inv (x : ℝ) (hx : 0 < x) : 1 ≤ max x x⁻¹ := by
  rcases le_total 1 x with h | h
  · exact le_max_of_le_left h
  · exact le_max_of_le_right ((one_le_inv₀ hx).2 h)

theorem list_prod (L : List ℕ) (f : ℕ → ℝ) (hf : ∀ l ∈ L, 1 ≤ f l) (a a' : ℝ) (ha : 0 ≤ a) (ha' : a ≤ a') :
    1 ≤ (L.map fun l => f l ^ a).prod ∧ (L.map fun l => f l ^ a).prod ≤ (L.map fun l => f l ^ a').prod := by
  induction L with
  | nil => simp
  | cons x L ih =>
    obtain ⟨i1, i2⟩ := ih fun l hl => hf l (by simp [hl])
    have hx : 1 ≤ f x := hf x (by simp)
    have h1 := Real.one_le_rpow hx ha
    have h2 := Real.rpow_le_rpow_of_exponent_le hx ha'
    simp only [List.map_cons, List.prod_cons]
    exact ⟨one_le_mul_of_one_le_of_one_le h1 i1, mul_le_mul h2 i2 (by linarith) (by linarith)⟩

theorem one_le_foldr (L : List ℝ) : 1 ≤ L.foldr max 1 := by
  induction L with
  | nil => simp
  | cons x L ih => exact le_max_of_le_right ih

theorem blockEnds_minors : ∀ (D : D7) (z z' : (Fin (2 * D.R.rS + D.R.k + 1) → ℂ)) (γ : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)), inWb D.R.k D.R.rS z → inWb D.R.k D.R.rS z' → 0 < Tz D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z' → RelPt D z z' γ p → (∀ l : ℕ, 1 ≤ l → (DminN z z' γ l ≠ 0 ↔ l ∈ ptBlockEnds p)) ∧ (ptBlockEnds p).Nodup ∧ (∀ l ∈ ptBlockEnds p, 1 ≤ l ∧ l ≤ D.R.rS + 1) ∧ D.R.rS + 1 ∈ ptBlockEnds p ∧ DminN z z' γ 0 = 1 ∧ 0 < Gf D.R.k D.R.rS z z' γ ∧ Gf D.R.k D.R.rS z z' γ ≤ ‖DminN z z' γ (D.R.rS + 1)‖ ^ 2 ∧ ∀ b C C₂ : ℝ, 1 ≤ b → 0 ≤ C → C ≤ C₂ → 1 ≤ lossV b C D.R.m z z' γ p ∧ lossV b C D.R.m z z' γ p ≤ lossV b C₂ D.R.m z z' γ p ∧ 1 ≤ lossP b C D.R.m z z' γ p ∧ lossP b C D.R.m z z' γ p ≤ lossP b C₂ D.R.m z z' γ p := by
  intro D z z' γ p hz hz' hT hT' hRel
  obtain ⟨hU, ⟨L, U, hL, hU', hZ⟩, hG⟩ := hRel
  have hp := p.2.1
  have hsum := p.2.2
  obtain ⟨e1, e2, e3⟩ := ends_bd p.1 hp 0
  rw [zero_add, hsum] at e1 e3
  have key : ∀ (l : ℕ) (hl : l ≤ D.R.rS + 1),
      Complex.normSq (DminN z z' γ l) = Complex.normSq (minor p.1 l) := by
    intro l hl
    have h1 := Formalism.MainNotions.S.Bridge.normSq_leadMinor_ZhatO D.R.k D.R.rS z z' γ l hl
    rw [hZ, Formalism.MainNotions.S.Bridge.leadMinor_cell L (ptMat p) U hL hU' l hl] at h1
    rw [DminN, dite_eq_left (Nat.lt_succ_of_le hl)]
    exact h1.symm
  have hiff : ∀ l : ℕ, 1 ≤ l → (DminN z z' γ l ≠ 0 ↔ l ∈ ptBlockEnds p) := by
    intro l hl
    by_cases hl' : l ≤ D.R.rS + 1
    · have h2 := minor_ne_iff p.1 hp 0 l hl
      rw [zero_add] at h2
      rw [Ne, ← Complex.normSq_eq_zero, key l hl', Complex.normSq_eq_zero]
      exact h2
    · rw [DminN, dite_eq_right (by omega)]
      exact ⟨fun h0 => absurd rfl h0, fun hm => absurd (e1 l hm).2 hl'⟩
  have hG0 : 0 < Gf D.R.k D.R.rS z z' γ :=
    lt_of_le_of_ne (Formalism.QuantumDeterminants.gNonneg D.R.k D.R.rS z z' hz hz' hT hT' γ hU) (Ne.symm hG)
  refine ⟨hiff, e2, fun l hl => e1 l hl, e3 fun h0 => ?_, ?_, hG0, ?_, fun b C C₂ hb hC hC2 => ?_⟩
  · rw [h0] at hsum
    simp at hsum
  · simp [DminN, Formalism.QuantumDeterminants.Dmin]
  · rw [DminN, dite_eq_left (by omega), ← Complex.normSq_eq_norm_sq]
    have := mul_nonneg (mul_pos hT hT').le
      (Complex.normSq_nonneg (Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS z z' γ ⟨D.R.rS, by omega⟩))
    exact sub_le_self _ this
  · have hm : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
    have hr : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
    have ex : ∀ x : ℝ, 0 ≤ x → 0 ≤ C * x ∧ C * x ≤ C₂ * x := fun x hx =>
      ⟨mul_nonneg hC hx, mul_le_mul_of_nonneg_right hC2 hx⟩
    obtain ⟨p1, p2⟩ := list_prod (ptBlockEnds p) (fun l => max ‖DminN z z' γ l‖ ‖DminN z z' γ l‖⁻¹)
      (fun l hl => one_le_max_inv _ (norm_pos_iff.2 ((hiff l (e1 l hl).1).2 hl))) _ _ (ex _ hm).1 (ex _ hm).2
    have g := one_le_max_inv _ hG0
    have a1 := Real.one_le_rpow hb (ex _ (pow_nonneg hm 4)).1
    have a2 := Real.rpow_le_rpow_of_exponent_le hb (ex _ (pow_nonneg hm 4)).2
    have g1 := Real.one_le_rpow g (ex _ (pow_nonneg hm 2)).1
    have g2 := Real.rpow_le_rpow_of_exponent_le g (ex _ (pow_nonneg hm 2)).2
    have c1 := Real.one_le_rpow hb (ex _ hm).1
    have c2 := Real.rpow_le_rpow_of_exponent_le hb (ex _ hm).2
    have f := one_le_foldr ((ptBlockEnds p).map fun l => max 1 ‖DminN z z' γ l‖⁻¹)
    have q1 := one_le_mul_of_one_le_of_one_le c1 f
    have q2 := mul_le_mul_of_nonneg_right c2 (zero_le_one.trans f)
    refine ⟨one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le a1 g1) p1, ?_,
      Real.one_le_rpow q1 (ex _ (pow_nonneg hr 3)).1, ?_⟩
    · exact mul_le_mul (mul_le_mul a2 g2 (by linarith) (by linarith)) p2 (by linarith)
        (mul_nonneg (by linarith) (by linarith))
    · exact (Real.rpow_le_rpow (by linarith) q2 (ex _ (pow_nonneg hr 3)).1).trans
        (Real.rpow_le_rpow_of_exponent_le (q1.trans q2) (ex _ (pow_nonneg hr 3)).2)

end GlobalTheory.Amp.PtMinor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetRealSandwich
section
namespace GlobalTheory.DeterminantRealSandwich

open Matrix

noncomputable def rowAct {j : ℕ} (C : Matrix (Fin j) (Fin j) ℂ) :
    (Fin j → Fin j → ℂ) →ₗ[ℂ] (Fin j → Fin j → ℂ) :=
  LinearMap.pi fun a => Matrix.toLin' C ∘ₗ LinearMap.proj a

theorem det_rowAct {j : ℕ} (C : Matrix (Fin j) (Fin j) ℂ) :
    LinearMap.det (rowAct C) = C.det ^ j := by
  unfold rowAct
  rw [LinearMap.det_pi (fun _ : Fin j => Matrix.toLin' C)]
  simp [LinearMap.det_toLin']

def swapIdx (j : ℕ) : (Fin j → Fin j → ℂ) ≃ₗ[ℂ] (Fin j → Fin j → ℂ) where
  toFun h := fun a b => h b a
  invFun h := fun a b => h b a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def sandwich {j : ℕ} (A B : Matrix (Fin j) (Fin j) ℂ) :
    (Fin j → Fin j → ℂ) →ₗ[ℂ] (Fin j → Fin j → ℂ) :=
  rowAct Bᵀ ∘ₗ ((swapIdx j).toLinearMap ∘ₗ rowAct A ∘ₗ (swapIdx j).symm.toLinearMap)

theorem det_sandwich {j : ℕ} (A B : Matrix (Fin j) (Fin j) ℂ) :
    LinearMap.det (sandwich A B) = B.det ^ j * A.det ^ j := by
  unfold sandwich
  rw [LinearMap.det_comp, LinearMap.det_conj, det_rowAct, det_rowAct, Matrix.det_transpose]

theorem sandwich_apply {j : ℕ} (A B : Matrix (Fin j) (Fin j) ℂ) (h : Fin j → Fin j → ℂ)
    (a b : Fin j) : sandwich A B h a b = (A * Matrix.of h * B) a b := by
  simp [sandwich, rowAct, swapIdx, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

theorem det_real_sandwich {j : ℕ} (A B : Matrix (Fin j) (Fin j) ℂ) :
    LinearMap.det ((sandwich A B).restrictScalars ℝ) = (‖A.det‖ ^ 2 * ‖B.det‖ ^ 2) ^ j := by
  rw [LinearMap.det_restrictScalars, det_sandwich, Algebra.norm_complex_apply, map_mul, map_pow,
    map_pow, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, mul_pow, mul_comm]

theorem det_real_family (ι : Type) [Fintype ι] (j : ℕ) (A B : ι → Matrix (Fin j) (Fin j) ℂ)
    (L : (ι → Fin j → Fin j → ℂ) →ₗ[ℝ] ι → Fin j → Fin j → ℂ)
    (hL : ∀ (h : ι → Fin j → Fin j → ℂ) (w : ι),
      Matrix.of (L h w) = A w * Matrix.of (h w) * B w) :
    LinearMap.det L = ∏ w : ι, (‖(A w).det‖ ^ 2 * ‖(B w).det‖ ^ 2) ^ j := by
  have e : L = LinearMap.pi fun w =>
      ((sandwich (A w) (B w)).restrictScalars ℝ) ∘ₗ LinearMap.proj w := by
    refine LinearMap.ext fun h => funext fun w => funext fun a => funext fun b => ?_
    have h1 : L h w a b = (A w * Matrix.of (h w) * B w) a b := by
      rw [← hL h w]; rfl
    rw [h1, ← sandwich_apply]
    rfl
  rw [e, LinearMap.det_pi (fun w => (sandwich (A w) (B w)).restrictScalars ℝ)]
  exact Finset.prod_congr rfl fun w _ => det_real_sandwich _ _

end GlobalTheory.DeterminantRealSandwich
end

