module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0872
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryOsc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0952
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumberFieldInvolutionSimilitudeCentralizer
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CentSim

variable {p : ℕ} [Fact p.Prime]

theorem commute_conj_sh_sim (G : HTGroup p) (β γ : G.Cˣ) (c₀ : ℚ)
    (h : (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c₀ * β) (z : G.C) (hz : Commute z (γ : G.C)) :
    Commute ((β : G.C) * sh G z * ((β⁻¹ : G.Cˣ) : G.C)) (γ : G.C) := by
  set y : G.Cˣ := γ with hydef
  set c : G.C := algebraMap ℚ G.C c₀
  set Y := sh G (y : G.C)
  set Yi := sh G ((y⁻¹ : G.Cˣ) : G.C)
  have hYYi : Y * Yi = 1 := by
    simp only [Y, Yi, ← GlobalTheory.CentConj.sh_mul', Units.inv_mul, GlobalTheory.CentConj.sh_one']
  have hzi : Commute z ((y⁻¹ : G.Cˣ) : G.C) := hz.units_inv_right
  have hcomm : Yi * sh G z = sh G z * Yi := by
    simp only [Yi, ← GlobalTheory.CentConj.sh_mul']; rw [hzi.eq]
  have hcc : ∀ w : G.C, c * w = w * c := fun w => Algebra.commutes _ w
  have h1 : (y : G.C) * β = c * β * Yi := by
    calc (y : G.C) * β = (y : G.C) * β * (Y * Yi) := by rw [hYYi, mul_one]
      _ = c * β * Yi := by rw [← mul_assoc, h]
  have h2 : ((β⁻¹ : G.Cˣ) : G.C) * y = c * Yi * ((β⁻¹ : G.Cˣ) : G.C) := by
    calc ((β⁻¹ : G.Cˣ) : G.C) * y = ((β⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * β) * ((β⁻¹ : G.Cˣ) : G.C) := by
          simp only [mul_assoc, Units.mul_inv, mul_one]
      _ = c * Yi * ((β⁻¹ : G.Cˣ) : G.C) := by
          rw [h1, ← mul_assoc, ← mul_assoc, ← hcc, mul_assoc c, Units.inv_mul, mul_one]
  change (β : G.C) * sh G z * ((β⁻¹ : G.Cˣ) : G.C) * y = y * ((β : G.C) * sh G z * ((β⁻¹ : G.Cˣ) : G.C))
  calc (β : G.C) * sh G z * ((β⁻¹ : G.Cˣ) : G.C) * y
        = (β : G.C) * sh G z * (((β⁻¹ : G.Cˣ) : G.C) * y) := by rw [mul_assoc]
    _ = c * (β * (sh G z * Yi)) * ((β⁻¹ : G.Cˣ) : G.C) := by
        rw [h2]; simp only [mul_assoc]
        rw [← mul_assoc (sh G z) c, ← hcc (sh G z), mul_assoc c, ← mul_assoc (β : G.C) c, ← hcc (β : G.C)]
        simp only [mul_assoc]
    _ = c * (β * (Yi * sh G z)) * ((β⁻¹ : G.Cˣ) : G.C) := by rw [hcomm]
    _ = (y : G.C) * β * sh G z * ((β⁻¹ : G.Cˣ) : G.C) := by rw [h1]; simp only [mul_assoc]
    _ = _ := by simp only [mul_assoc]

theorem centraliser_field_involution : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β γ : G.Cˣ) (c₀ : ℚˣ), sh G β = β →
    (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c₀ * β → Irreducible (minpoly G.F (γ : G.C)) →
    (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L),
      Function.Injective ι ∧ (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) ∧
      (∀ x, ι (c x) = β * sh G (ι x) * ((β⁻¹ : G.Cˣ) : G.C)) ∧ ∀ x, c (c x) = x := by
  intro p _ G β γ c₀ hβ hsim hirr hdeg
  obtain ⟨E, _, _, _, j, hj, hcent⟩ := GlobalTheory.CentIrr.centralizer_unit_eq_field p G γ hirr hdeg
  set w : E → G.C := fun e => (β : G.C) * sh G (j e) * ((β⁻¹ : G.Cˣ) : G.C) with hw
  have hex : ∀ e, ∃ e', j e' = w e := fun e =>
    (hcent _).1 (commute_conj_sh_sim G β γ (c₀ : ℚ) hsim (j e) ((hcent _).2 ⟨e, rfl⟩))
  choose t ht using hex
  have tt : ∀ e, t (t e) = e := by
    intro e
    apply hj
    rw [ht, hw]; dsimp only
    rw [ht, GlobalTheory.CentConj.sh_mul', GlobalTheory.CentConj.sh_mul', GlobalTheory.CentConj.sh_sh', hβ,
      GlobalTheory.CentConj.sh_inv_of_sym G β hβ]
    simp only [mul_assoc, Units.mul_inv, mul_one]
    rw [← mul_assoc, Units.mul_inv, one_mul]
  have hm : ∀ a b, t (a * b) = t a * t b := by
    intro a b
    apply hj
    rw [mul_comm a b, ht, map_mul, ht, ht, hw]; dsimp only
    rw [map_mul, GlobalTheory.CentConj.sh_mul']
    simp only [mul_assoc]
    rw [← mul_assoc ((β⁻¹ : G.Cˣ) : G.C) (β : G.C), Units.inv_mul, one_mul]
  have ha : ∀ a b, t (a + b) = t a + t b := by
    intro a b
    apply hj
    rw [ht, map_add (f := _), ht, ht, hw]; dsimp only
    rw [map_add (f := _), GlobalTheory.CentConj.sh_add']; noncomm_ring
  have h1 : t 1 = 1 := by
    apply hj
    rw [ht, hw]; dsimp only
    rw [map_one, GlobalTheory.CentConj.sh_one', mul_one, Units.mul_inv]
  have h0 : t 0 = 0 := by
    have h := ha 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  let τ : E →+* E := { toFun := t, map_one' := h1, map_mul' := hm, map_zero' := h0, map_add' := ha }
  refine ⟨E, inferInstance, inferInstance, j.toRingHom.toRatAlgHom, τ.toRatAlgHom, hj, ?_, ?_, ?_⟩
  · intro z
    exact hcent z
  · intro x; exact ht x
  · intro x; exact tt x

end GlobalTheory.CentSim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalComplementEmbeddingHyperbolicPai
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory

theorem exists_orthCompl_hypPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E),
    n = n₁ + 2 → (∀ i j, σ (J j i) = J i j) → form σ J x x = 0 → form σ J y y = 0 → form σ J x y = 1 →
    ∃ (ι : Matrix (Fin n) (Fin n₁) E) (P : Matrix (Fin n₁) (Fin n) E), P * ι = 1 ∧
      (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) ∧
      ∀ z, form σ J z x = 0 → form σ J z y = 0 → ∃ u, z = ι *ᵥ u := by
  intro F E _ _ _ _ _ σ n n₁ J x y hn hJ hxx hyy hxy
  classical
  set a : Fin n → E := J *ᵥ fun i => σ (x i) with ha_def
  set b : Fin n → E := J *ᵥ fun i => σ (y i) with hb_def
  have hfa : ∀ z, form σ J z x = z ⬝ᵥ a := fun z => rfl
  have hfb : ∀ z, form σ J z y = z ⬝ᵥ b := fun z => rfl
  have hxa : x ⬝ᵥ a = 0 := hxx
  have hxb : x ⬝ᵥ b = 1 := hxy
  have ha : a ≠ 0 := by
    intro h0
    have hv : x ᵥ* J = 0 := by
      funext j
      apply σ.toRingHom.injective
      have h1 := congrFun h0 j
      simp only [ha_def, Matrix.mulVec, dotProduct, Pi.zero_apply] at h1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, map_zero, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul]
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hJ j i, mul_comm]
    apply one_ne_zero (α := E)
    rw [← hxb, hb_def, Matrix.dotProduct_mulVec, hv, zero_dotProduct]
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push_neg at h; exact ha (funext h)
  set w : Fin n → E := (a i)⁻¹ • (Pi.single i 1 - (b i) • x) with hw
  have hwa : w ⬝ᵥ a = 1 := by
    rw [hw, smul_dotProduct, sub_dotProduct, smul_dotProduct, hxa, single_dotProduct]
    simp [hi]
  have hwb : w ⬝ᵥ b = 0 := by
    rw [hw, smul_dotProduct, sub_dotProduct, smul_dotProduct, hxb, single_dotProduct]
    simp
  let M : Matrix (Fin 2) (Fin n) E := Matrix.of ![a, b]
  have hM : ∀ z, M *ᵥ z = ![z ⬝ᵥ a, z ⬝ᵥ b] := by
    intro z; funext k; fin_cases k <;> simp [M, Matrix.mulVec, dotProduct_comm]
  have hsurj : LinearMap.range (Matrix.mulVecLin M) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro v
    refine ⟨v 0 • w + v 1 • x, ?_⟩
    rw [Matrix.mulVecLin_apply, hM]
    funext k; fin_cases k <;> simp [add_dotProduct, smul_dotProduct, hwa, hwb, hxa, hxb]
  have hrank : Module.finrank E (LinearMap.ker (Matrix.mulVecLin M)) = n₁ := by
    have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin M)
    rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
    omega
  set K := LinearMap.ker (Matrix.mulVecLin M) with hK
  have hmemK : ∀ z, z ∈ K ↔ z ⬝ᵥ a = 0 ∧ z ⬝ᵥ b = 0 := by
    intro z
    rw [hK, LinearMap.mem_ker, Matrix.mulVecLin_apply, hM]
    constructor
    · intro h; exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
    · rintro ⟨h1, h2⟩; funext k; fin_cases k <;> simp [h1, h2]
  let bK : Module.Basis (Fin n₁) E K := Module.finBasisOfFinrankEq E K hrank
  let f : (Fin n₁ → E) →ₗ[E] (Fin n → E) := K.subtype ∘ₗ bK.equivFun.symm.toLinearMap
  have hfinj : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective.comp bK.equivFun.symm.injective
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hfinj
  refine ⟨LinearMap.toMatrix' f, LinearMap.toMatrix' g, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  · intro u
    rw [LinearMap.toMatrix'_mulVec, hfa, hfb]
    exact (hmemK _).1 (bK.equivFun.symm u).2
  · intro z h1 h2
    have hz : z ∈ K := (hmemK z).2 ⟨h1, h2⟩
    refine ⟨bK.equivFun ⟨z, hz⟩, ?_⟩
    rw [LinearMap.toMatrix'_mulVec]
    simp [f]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionNormalisingSchrodinger
section
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil Matrix

noncomputable section

namespace GlobalTheory.HoweD.Osc

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}

abbrev Lines (P Q R S : ι → ℕ) := Σ o : (Σ w : ι, Ix (P w) (Q w)), Ix (R o.1) (S o.1)

def lineSgn (n : Lines P Q R S) : Bool :=
  linePos (p := P n.1.1) (q := Q n.1.1) (r := R n.1.1) (s := S n.1.1) (n.1.2, n.2)

theorem blockDiagonal'_mulVec_apply {m : (Σ w : ι, Ix (P w) (Q w)) → Type} [∀ o, Fintype (m o)]
    [∀ o, DecidableEq (m o)] (M : ∀ o, Matrix (m o) (m o) ℂ) (v : (Σ o, m o) → ℂ) (o : Σ w : ι, Ix (P w) (Q w))
    (b : m o) : (blockDiagonal' M *ᵥ v) ⟨o, b⟩ = ∑ b', M o b b' * v ⟨o, b'⟩ := by
  simp only [mulVec, dotProduct]
  rw [Fintype.sum_sigma, Finset.sum_eq_single o]
  · simp [blockDiagonal'_apply']
  · intro o' _ h
    simp [blockDiagonal'_apply_ne M b _ (Ne.symm h)]
  · simp

theorem diagonal_lineSgn : (diagonal fun n : Lines P Q R S => if lineSgn n then (1 : ℂ) else -1) =
    blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => Jm (P o.1) (Q o.1) o.2 o.2 • Jm (R o.1) (S o.1) := by
  ext ⟨o, b⟩ ⟨o', b'⟩
  by_cases h : o = o'
  · subst h
    rcases o with ⟨w, a⟩
    rw [blockDiagonal'_apply']
    rcases a with a | a <;> rcases b with b | b <;> rcases b' with b' | b' <;>
      simp [diagonal_apply, Jm, Formalism.UG.Jpq, lineSgn, linePos, Matrix.one_apply] <;> split_ifs <;> simp_all
  · rw [blockDiagonal'_apply_ne _ _ _ h, diagonal_apply_ne]
    intro e
    exact h (congrArg Sigma.fst e)

theorem blockDiagonal'_mem (M : ∀ w, Mat (R w) (S w)) (hM : ∀ w, (M w)ᴴ * Jm (R w) (S w) * M w = Jm (R w) (S w)) :
    (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => M o.1)ᵀ *
        (diagonal fun n : Lines P Q R S => if lineSgn n then (1 : ℂ) else -1) *
        (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => M o.1).map star =
      diagonal fun n : Lines P Q R S => if lineSgn n then (1 : ℂ) else -1 := by
  rw [diagonal_lineSgn, blockDiagonal'_transpose, blockDiagonal'_map _ _ (star_zero ℂ), ← blockDiagonal'_mul,
    ← blockDiagonal'_mul]
  congr 1
  funext o
  have h := congrArg transpose (hM o.1)
  rw [transpose_mul, transpose_mul, GlobalTheory.SchrodOsc.Jm_transpose] at h
  have e : (M o.1)ᴴᵀ = (M o.1).map star := by ext; simp
  rw [e] at h
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, h]

end GlobalTheory.HoweD.Osc

namespace GlobalTheory.HoweD.Osc

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ} {G : Type} [Group G]

abbrev lineNum (P Q R S : ι → ℕ) := GlobalTheory.SchrodOsc.signEquiv (lineSgn (P := P) (Q := Q) (R := R) (S := S))

abbrev NumIx (P Q R S : ι → ℕ) :=
  Fin (Fintype.card {n // lineSgn (P := P) (Q := Q) (R := R) (S := S) n = true}) ⊕
    Fin (Fintype.card {n // ¬ lineSgn (P := P) (Q := Q) (R := R) (S := S) n = true})

def blockHom (P Q : ι → ℕ) (k : G →* (∀ w, Mat (R w) (S w))) : G →* Matrix (Lines P Q R S) (Lines P Q R S) ℂ where
  toFun g := blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1
  map_one' := by
    simp only [map_one, Pi.one_apply]
    exact blockDiagonal'_one
  map_mul' g g' := by simp [blockDiagonal'_mul]

def numHom (P Q : ι → ℕ) (k : G →* (∀ w, Mat (R w) (S w))) : G →* Matrix (NumIx P Q R S) (NumIx P Q R S) ℂ :=
  (reindexAlgEquiv ℂ ℂ (lineNum P Q R S)).toAlgHom.toRingHom.toMonoidHom.comp (blockHom P Q k)

theorem numHom_apply (k : G →* (∀ w, Mat (R w) (S w))) (g : G) :
    numHom P Q k g = reindex (lineNum P Q R S) (lineNum P Q R S)
      (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1) :=
  rfl

theorem numHom_mem (k : G →* (∀ w, Mat (R w) (S w))) (hk : ∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w))
    (g : G) :
    (numHom P Q k).toHomUnits g ∈ GlobalTheory.WeilM.UG (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) (fromBlocks 1 0 0 (-1)) := by
  have hc : ⇑(Complex.conjAe : ℂ →ₐ[ℝ] ℂ) = star := funext fun x => by simp
  show (numHom P Q k g)ᵀ * fromBlocks 1 0 0 (-1) * (numHom P Q k g).map (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) =
    fromBlocks 1 0 0 (-1)
  rw [hc, numHom_apply, GlobalTheory.SchrodOsc.fromBlocks_eq_reindex, transpose_reindex]
  have hm : (reindex (lineNum P Q R S) (lineNum P Q R S)
      (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1)).map star =
      reindex (lineNum P Q R S) (lineNum P Q R S)
        ((blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1).map star) := rfl
  rw [hm, ← reindexAlgEquiv_apply ℂ ℂ, ← reindexAlgEquiv_apply ℂ ℂ, ← reindexAlgEquiv_apply ℂ ℂ, ← map_mul, ← map_mul,
    blockDiagonal'_mem _ (hk g)]

def unitHom (P Q : ι → ℕ) (k : G →* (∀ w, Mat (R w) (S w)))
    (hk : ∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) :=
  (numHom P Q k).toHomUnits.codRestrict _ (numHom_mem k hk)

theorem continuous_unitHom [TopologicalSpace G] [IsTopologicalGroup G] (k : G →* (∀ w, Mat (R w) (S w)))
    (hc : Continuous k) (hk : ∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) :
    Continuous (unitHom P Q k hk) := by
  have hn : Continuous (numHom P Q k) := by
    show Continuous fun g => reindex (lineNum P Q R S) (lineNum P Q R S)
      (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1)
    exact (Continuous.matrix_blockDiagonal'
      (continuous_pi fun (o : Σ w : ι, Ix (P w) (Q w)) => (continuous_apply o.1).comp hc)).matrix_reindex _ _
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨hn, ?_⟩)
  have : (fun g => (((Subtype.val ∘ unitHom P Q k hk) g)⁻¹ : GL _ ℂ).val) = fun g => numHom P Q k g⁻¹ := by
    funext g
    simp only [Function.comp_apply]
    rw [← Subgroup.coe_inv, ← map_inv]
    rfl
  rw [this]
  exact hn.comp continuous_inv

def coordOf (z : NumIx P Q R S → ℂ) : ∀ w, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ :=
  fun w a b => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * z (lineNum P Q R S ⟨⟨w, a⟩, b⟩)

theorem coordOf_add (z z' : NumIx P Q R S → ℂ) : coordOf (z + z') = coordOf z + coordOf z' := by
  funext w a b
  simp [coordOf, mul_add]

theorem continuous_coordOf : Continuous (coordOf (P := P) (Q := Q) (R := R) (S := S)) :=
  continuous_pi fun _ => continuous_pi fun _ => continuous_pi fun _ => continuous_const.mul (continuous_apply _)

theorem two_mul_sum_coordOf (z z' : NumIx P Q R S → ℂ) :
    2 * ∑ w, ∑ a, ∑ b, lineSign a b * coordOf z w a b * star (coordOf z' w a b) =
      (∑ i, z (Sum.inl i) * star (z' (Sum.inl i))) - ∑ j, z (Sum.inr j) * star (z' (Sum.inr j)) := by
  set e := lineNum P Q R S with he
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = 2⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]
    push_cast
    rfl
  let F : Lines P Q R S → ℂ := fun n => (if lineSgn n then 1 else -1) * z (e n) * star (z' (e n))
  have h1 : ∀ w a b, lineSign a b * coordOf z w a b * star (coordOf z' w a b) = 2⁻¹ * F ⟨⟨w, a⟩, b⟩ := by
    intro w a b
    simp only [coordOf, F, star_mul, lineSgn, GlobalTheory.SchrodOsc.lineSign_eq]
    rw [← hs, he]
    by_cases h : linePos (a, b) = true <;> simp only [h, ↓reduceIte, Bool.false_eq_true] <;> ring
  have h2 : ∑ n, F n = ∑ w, ∑ a, ∑ b, F ⟨⟨w, a⟩, b⟩ := by
    rw [Fintype.sum_sigma, Fintype.sum_sigma]
  have h3 : ∑ n, F n = ∑ i, F (e.symm i) := (e.symm.sum_comp F).symm
  simp_rw [h1, ← Finset.mul_sum, ← h2, h3, Fintype.sum_sum_type]
  simp only [F, he, GlobalTheory.SchrodOsc.pos_signEquiv_symm_inl, GlobalTheory.SchrodOsc.pos_signEquiv_symm_inr,
    Equiv.apply_symm_apply]
  simp
  ring

theorem coordOf_mulVec (k : G →* (∀ w, Mat (R w) (S w)))
    (hk : ∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) (g : G) (z : NumIx P Q R S → ℂ) :
    coordOf (((unitHom P Q k hk g).1 : Matrix _ _ ℂ) *ᵥ z) = fun w => coordOf z w * (k g w)ᵀ := by
  show coordOf (numHom P Q k g *ᵥ z) = _
  rw [numHom_apply, reindex_apply, submatrix_mulVec_equiv]
  funext w
  ext a b
  simp only [coordOf, Function.comp_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  rw [blockDiagonal'_mulVec_apply]
  simp only [mul_apply, transpose_apply, Finset.mul_sum, Function.comp_apply]
  exact Finset.sum_congr rfl fun _ _ => by simp only [coordOf, transpose_apply]; ring

end GlobalTheory.HoweD.Osc

open GlobalTheory.HoweD

theorem GlobalTheory.HoweD.exists_osc : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    (∀ v : L2 l, Continuous fun w : l ⊕ l → ℝ => rho w v) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (k : G →* (∀ w : ι, Mat (R w) (S w))), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) →
    ∃ ω : G →* (L2 l ≃ₗᵢ[ℂ] L2 l), (∀ v, Continuous fun g => ω g v) ∧
      ∀ g c v, ω g (rho (φ c) v) = rho (φ fun w => c w * (k g w)ᵀ) (ω g v) := by
  intro ι l _ _ _ _ P Q R S φ hφ hcont G _ _ _ k hkc hk
  obtain ⟨ω₀, hω₀c, hω₀, -⟩ := GlobalTheory.FockRep.exists_unitary_osc _ _ (L2 l)
    (fun z => rho (φ (GlobalTheory.HoweD.Osc.coordOf z)))
    (fun v => (hcont v).comp ((LinearMap.continuous_of_finiteDimensional φ.toLinearMap).comp
      GlobalTheory.HoweD.Osc.continuous_coordOf))
    (fun z z' v => by
      rw [rho_rho, ← map_add (f := _), ← GlobalTheory.HoweD.Osc.coordOf_add, hφ, ← GlobalTheory.HoweD.Osc.two_mul_sum_coordOf]
      congr 2
      simp [Complex.mul_im]
      ring)
  refine ⟨ω₀.comp (GlobalTheory.HoweD.Osc.unitHom P Q k hk), fun v => (hω₀c v).comp (GlobalTheory.HoweD.Osc.continuous_unitHom k hkc hk),
    fun g c v => ?_⟩
  obtain ⟨z, hz⟩ : ∃ z, GlobalTheory.HoweD.Osc.coordOf (P := P) (Q := Q) (R := R) (S := S) z = c := by
    refine ⟨fun i => ((Real.sqrt 2 : ℝ) : ℂ) * (fun n : GlobalTheory.HoweD.Osc.Lines P Q R S => c n.1.1 n.1.2 n.2)
      ((GlobalTheory.HoweD.Osc.lineNum P Q R S).symm i), ?_⟩
    funext w a b
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 two_pos).ne'
    simp only [GlobalTheory.HoweD.Osc.coordOf]
    rw [Equiv.symm_apply_apply, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]
  have h := hω₀ (GlobalTheory.HoweD.Osc.unitHom P Q k hk g) z v
  rw [hz, GlobalTheory.HoweD.Osc.coordOf_mulVec, hz] at h
  exact h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarDecompositionIndefiniteUnitaryStatement
section
open scoped Matrix
open Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polar_decomposition_indefiniteUnitary : ∀ (R S : ℕ) (u : Mat R S), uᴴ * Jm R S * u = Jm R S → ∃ k q : Mat R S, kᴴ * Jm R S * k = Jm R S ∧
    Jm R S * k = k * Jm R S ∧ qᴴ * Jm R S * q = Jm R S ∧ Jm R S * q * Jm R S * q = 1 ∧ u = k * q * q := by
  first | exact @GlobalTheory.UnitaryPolar.polar | exact GlobalTheory.UnitaryPolar.polar | (intros; apply GlobalTheory.UnitaryPolar.polar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPsiOfOverK
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift

theorem overK_of_sqrt {D : D7} (σ : D.what₂.LL →+* ℂ)
    (h : σ (D.embE D.host.sqrtMinusD) = D.what₂.embLL (D.embE D.host.sqrtMinusD)) : OverK σ := by
  intro x hx
  have hx' : x ∈ IntermediateField.adjoin ℚ {D.host.sqrtMinusD} := hx
  clear hx
  induction hx' using IntermediateField.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact h
  | algebraMap q => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  | inv x _ hx => rw [map_inv₀, map_inv₀, map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, map_mul, hx, hy]

theorem embLL_embE (D : D7) (x : D.host.E) : D.what₂.embLL (D.embE x) = D.host.φ₀ x :=
  RingHom.congr_fun D.embE_φ₀ x

theorem sqrtMinusD_sq (D : D7) : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) :=
  D.host.sqd_sq

theorem overK_conj {D : D7} (σ : D.what₂.LL →+* ℂ) (h : ¬ OverK σ) : OverK ((starRingEnd ℂ).comp σ) := by
  apply overK_of_sqrt
  have h0 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have h1 : σ (D.embE D.host.sqrtMinusD) ^ 2 = D.what₂.embLL (D.embE D.host.sqrtMinusD) ^ 2 := by
    rw [← map_pow, ← map_pow, ← map_pow, ← map_pow, sqrtMinusD_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
  · exact absurd (overK_of_sqrt σ h2) h
  · rw [RingHom.comp_apply, h2, embLL_embE, h0]; simp

theorem exists_psi_of_overK {D : D7} (σ : D.what₂.LL →+* ℂ) (h : OverK σ) :
    ∃ g ∈ D.R.Psi, ∀ τ, labE σ τ = D.host.emb (g * (D.eTau τ).1) := by
  obtain ⟨g0, h0⟩ := (factEmb D.R D.host).1.2 (σ.comp D.embE)
  refine ⟨g0, ((factEmb D.R D.host).2 _).1 ?_, fun τ => ?_⟩
  · have h1 := h D.host.sqrtMinusD (IntermediateField.mem_adjoin_simple_self ℚ _)
    have h2 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
    rw [h0]
    exact h1.trans ((embLL_embE D _).trans h2)
  · rw [ConjReading.emb_mul, h0]; rfl

theorem labels_overK : ∀ {D : D7} (σ : D.what₂.LL →+* ℂ),
    (OverK σ → Function.Bijective (lab (D := D) σ) ∧ ∀ ρ, labE σ (lab σ ρ) = tauE D ρ) ∧
      (¬ OverK σ → OverK ((starRingEnd ℂ).comp σ)) := by
  intro D σ
  refine ⟨fun h => ?_, overK_conj σ⟩
  obtain ⟨g, hg, key⟩ := exists_psi_of_overK σ h
  have inj := (factEmb D.R D.host).1.1
  have main : ∀ ρ, labE σ (lab σ ρ) = tauE D ρ := by
    intro ρ
    have hs : labE σ (lab σ ρ) = tauE D ρ ∨ labE σ (lab σ ρ) = (starRingEnd ℂ).comp (tauE D ρ) := by
      unfold lab; rw [dite_eq_left (ConjReading.lab_exists σ ρ)]; exact (ConjReading.lab_exists σ ρ).choose_spec
    refine hs.resolve_right fun h' => ?_
    rw [key] at h'
    exact ConjReading.conj_not_mem D ρ _ h' (Subgroup.mul_mem _ hg (D.eTau _).2)
  refine ⟨⟨fun ρ ρ' e => ?_, fun τ => ?_⟩, main⟩
  · have e' : tauE D ρ = tauE D ρ' := by rw [← main, ← main, e]
    exact D.eTau.injective (Subtype.ext (inj e'))
  · refine ⟨D.eTau.symm ⟨g * (D.eTau τ).1, Subgroup.mul_mem _ hg (D.eTau τ).2⟩, ?_⟩
    have e := main (D.eTau.symm ⟨g * (D.eTau τ).1, Subgroup.mul_mem _ hg (D.eTau τ).2⟩)
    rw [key, tauE, Equiv.apply_symm_apply] at e
    exact D.eTau.injective (Subtype.ext (mul_left_cancel (inj e)))

end GlobalTheory.GalLift
end

