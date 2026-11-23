module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreEnvelopingAlgebraCommuteRealLieSmoothing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0853
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1331
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1323
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliKilledSlowlyIncreasingSmoothingMem
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth

noncomputable section

open GlobalTheory.AutGrowth.SmoothFinite

namespace GlobalTheory.CapKilledSmooth

theorem smoothing_mem_space : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ) (ν : Measure (Lie E b)) [ν.IsAddHaarMeasure] (α : Lie E b → ℂ), IsTest (invSet E b) α → KInv α → ∀ (L : Subgroup (GL (Fin b) (Af E))) (W : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ W → ∀ (q : (E →+* ℂ) → ℂ → Polynomial ℂ) (ψ : Sm E b), ψ ∈ leftInv E b ⊓ fixL E b L ⊓ GlobalTheory.CapKilled.ktype E b W ⊓ GlobalTheory.CapKilled.killed E b q → ψ.1 ∈ growth E b → ∃ h : smoothing ν α ψ.1 ∈ Sm E b, (⟨smoothing ν α ψ.1, h⟩ : Sm E b) ∈ GlobalTheory.CapKilled.space E b L W q := by
  intro E _ _ _ b ν _ α hα hK L W hW q ψ hψ hg
  obtain ⟨⟨⟨hl, hL⟩, hk⟩, hq⟩ := hψ
  have h := GlobalTheory.T.realLieSmoothing_mem_smoothAdelicFunctions E b ν α hα ψ.1 ψ.2
  refine ⟨h, GlobalTheory.CapKilled.mem_space.2 ⟨fun γ g => ?_, fun k hk' => ?_, fun g => ?_, fun τ u => ?_, fun l => ?_⟩⟩
  · show smoothing ν α ψ.1 (ratGL E b γ * g) = smoothing ν α ψ.1 g
    have hl' : ∀ γ g, ψ.1 (ratGL E b γ * g) = ψ.1 g := hl
    simp only [smoothing, chart, mul_assoc, hl']
  · apply Subtype.ext; funext g
    show smoothing ν α ψ.1 (g * finGL E b k) = smoothing ν α ψ.1 g
    have hw : (fun x => ψ.1 (x * finGL E b k)) = ψ.1 := congrArg Subtype.val (hL k hk')
    simp only [smoothing]
    rw [← chart_rt_fin, hw]
  · obtain ⟨s, c, hc⟩ := GlobalTheory.HCFct.exists_interp W hW
    have hpt : ∀ (k : Kinf E b) (x : GA E b), ψ.1 (x * infGL E b (Unitary.toUnits k)) =
        ∑ i : s, ψ.1 (x * infGL E b (Unitary.toUnits i.1)) * (c i).1 k := fun k x => hc _ (hk x) k
    have hfun : ∀ k : Kinf E b, (fun x => ψ.1 (x * infGL E b (Unitary.toUnits k))) =
        (∑ i : s, (c i).1 k • cptRep E b i.1 ψ : Sm E b).1 := by
      intro k; funext x
      rw [hpt k x, Submodule.coe_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
      rfl
    have e : (fun k : Kinf E b => (cptRep E b k ⟨smoothing ν α ψ.1, h⟩).1 g) =
        ∑ i : s, (smoothing ν α (cptRep E b i.1 ψ).1 g) • (c i).1 := by
      funext k
      have e1 : (cptRep E b k ⟨smoothing ν α ψ.1, h⟩).1 g =
          smoothing ν α ψ.1 (g * infGL E b (Unitary.toUnits k)) := rfl
      rw [e1, ← GlobalTheory.T.smoothing_right_translate_maxCompact E b ν α hK ψ.1 k g, hfun k]
      have hsum : ∀ (t : Finset s) (f : s → Sm E b),
          smoothing ν α (∑ i ∈ t, f i).1 = ∑ i ∈ t, smoothing ν α (f i).1 := by
        intro t f
        classical
        induction t using Finset.induction_on with
        | empty => funext x; simp [smoothing, chart]
        | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, smoothing_add ν hα, ih]
      rw [hsum, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smoothing_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
    rw [e]
    exact W.sum_mem fun i _ => W.smul_mem _ (c i).2
  · have hz : Polynomial.aeval (cap (a := b) τ u) (q τ u) ∈ Zalg E b := by
      show _ ∈ Algebra.adjoin ℂ _
      exact Algebra.adjoin_mono (s := {cap (a := b) τ u}) (by rintro _ rfl; exact ⟨τ, u, rfl⟩)
        (Polynomial.aeval_mem_adjoin_singleton ℂ _)
    apply Subtype.ext
    rw [_root_.GlobalTheory.CentreSmooth.zalg_smoothing E b ν α hα ψ h _ hz, (GlobalTheory.CapKilled.mem_killed.1 hq) τ u]
    funext g
    simp [smoothing, chart]
  · obtain ⟨β, hβ, e⟩ : ∃ β, IsTest (invSet E b) β ∧
        ((l.map (lie E b)).prod (⟨smoothing ν α ψ.1, h⟩ : Sm E b)).1 = smoothing ν β ψ.1 := by
      induction l with
      | nil => exact ⟨α, hα, rfl⟩
      | cons X l ih =>
        obtain ⟨β, hβ, e⟩ := ih
        refine ⟨dens X β, isTest_dens X hβ, funext fun g => ?_⟩
        rw [List.map_cons, List.prod_cons, Module.End.mul_apply, lie_apply, e]
        exact _root_.GlobalTheory.AutGrowth.lieD_smoothing_eq_dens E b ν β hβ ψ.1 ψ.2 X g
    rw [e]
    exact _root_.GlobalTheory.AutGrowth.smoothing_mem_growth E b ν β hβ ψ.1 hg

end GlobalTheory.CapKilledSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanInvolutionSystemsConjArchimedeanUnitary
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section
namespace GlobalTheory.ConjCartan


open scoped ComplexOrder in
theorem exists_conj_cartan_matrix : ∀ (n : ℕ) (M θ₁ θ₂ : Matrix (Fin n) (Fin n) ℂ), Mᴴ = M → IsCartan M θ₁ → IsCartan M θ₂ →
    ∃ u v : Matrix (Fin n) (Fin n) ℂ, u * v = 1 ∧ uᵀ * M * u.map star = M ∧ u * θ₁ = θ₂ * u := by
  intro n M θ₁ θ₂ hM h1 h2
  have key : ∀ θ, IsCartan M θ → θ.map star * θ.map star = 1 ∧ (θ.map star)ᴴ * M * θ.map star = M ∧
      (M * θ.map star).PosDef := by
    rintro θ ⟨hθ, hu, hp⟩
    have hS : θ.map star = θᵀᴴ := rfl
    have hT : (θ.map star)ᴴ = θᵀ := by rw [hS, Matrix.conjTranspose_conjTranspose]
    have hSS : θ.map star * θ.map star = 1 := by
      rw [hS, ← Matrix.conjTranspose_mul, ← Matrix.transpose_mul, hθ, Matrix.transpose_one, Matrix.conjTranspose_one]
    have hMS : M * θ.map star = θᵀ * M := by
      calc M * θ.map star = θᵀ * M * θ.map star * θ.map star := by rw [hu]
        _ = θᵀ * M := by rw [Matrix.mul_assoc _ (θ.map star), hSS, Matrix.mul_one]
    have hH : (M * θ.map star)ᴴ = M * θ.map star := by
      rw [Matrix.conjTranspose_mul, hT, hM, hMS]
    refine ⟨hSS, by rw [hT]; exact hu, ?_⟩
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨hH, fun x hx => ?_⟩
    have hx' : star x ≠ 0 := by simpa using hx
    have hre := hp (star x) hx'
    have e1 : star x ⬝ᵥ (M * θ.map star) *ᵥ x = (θ *ᵥ star x) ⬝ᵥ M *ᵥ star (star x) := by
      rw [star_star, hMS, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    have e2 : star (star x ⬝ᵥ (M * θ.map star) *ᵥ x) = star x ⬝ᵥ (M * θ.map star) *ᵥ x := by
      conv_rhs => rw [Matrix.star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH]
    rw [Complex.lt_def]
    refine ⟨by rw [e1]; simpa using hre, ?_⟩
    have h3 := congrArg Complex.im e2
    have h4 : (star (star x ⬝ᵥ (M * θ.map star) *ᵥ x)).im = -(star x ⬝ᵥ (M * θ.map star) *ᵥ x).im :=
      Complex.conj_im _
    rw [Complex.zero_im]; linarith
  obtain ⟨hs1, hs2, hs3⟩ := key θ₁ h1
  obtain ⟨ht1, ht2, ht3⟩ := key θ₂ h2
  set S₁ := θ₁.map star
  set S₂ := θ₂.map star
  obtain ⟨p, q, B, B', hBB, hB'B, hBG, hBs⟩ := GlobalTheory.exists_basis_adapted_to_cartan_involution n M S₁ hs1 hs2 hs3
  set D : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.fromBlocks 1 0 0 (-1)
  have hDh : Dᴴ = D := by simp [D, Matrix.fromBlocks_conjTranspose]
  have hDD : D * D = 1 := by simp [D, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  set T := B' * S₂ * B
  have hTT : T * T = 1 := by
    calc T * T = B' * S₂ * (B * B') * S₂ * B := by simp only [T, Matrix.mul_assoc]
      _ = 1 := by rw [hBB, Matrix.mul_one, Matrix.mul_assoc B', ht1, Matrix.mul_one, hB'B]
  have hinj : Function.Injective B.mulVec := fun x y hxy => by
    have := congrArg (B'.mulVec) hxy
    simpa [Matrix.mulVec_mulVec, hB'B] using this
  have hDT : (D * T).PosDef := by
    have h := ht3.conjTranspose_mul_mul_same hinj
    have e : Bᴴ * (M * S₂) * B = D * T := by
      calc Bᴴ * (M * S₂) * B = Bᴴ * M * (B * B') * S₂ * B := by rw [hBB]; simp only [Matrix.mul_assoc, Matrix.mul_one]
        _ = D * T := by rw [← hBG]; simp only [T, Matrix.mul_assoc]
    rwa [e] at h
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.cartanInvolution_conj_of_posDef _ D T hDh hDD hTT hDT

  have haL : (D * aᴴ * D) * a = 1 := by simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc aᴴ, ha1, hDD]
  set U := B * a * B'
  set V := B * (D * aᴴ * D) * B'
  have hVU : V * U = 1 := by
    calc V * U = B * (D * aᴴ * D) * (B' * B) * a * B' := by simp only [V, U, Matrix.mul_assoc]
      _ = 1 := by rw [hB'B, Matrix.mul_one, Matrix.mul_assoc B, haL, Matrix.mul_one, hBB]
  have hUU : Uᴴ * M * U = M := by
    have hBh : B'ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hBB, Matrix.conjTranspose_one]
    calc Uᴴ * M * U = B'ᴴ * (aᴴ * (Bᴴ * M * B) * a) * B' := by
          simp only [U, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = B'ᴴ * (Bᴴ * M * B) * B' := by rw [hBG, ha1]
      _ = (B'ᴴ * Bᴴ) * M * (B * B') := by simp only [Matrix.mul_assoc]
      _ = M := by rw [hBh, hBB, Matrix.one_mul, Matrix.mul_one]
  have hB'S : B' * S₁ = D * B' := by
    calc B' * S₁ = B' * S₁ * (B * B') := by rw [hBB, Matrix.mul_one]
      _ = B' * (S₁ * B) * B' := by simp only [Matrix.mul_assoc]
      _ = B' * (B * D) * B' := congrArg (fun Z => B' * Z * B') hBs
      _ = (B' * B) * D * B' := by simp only [Matrix.mul_assoc]
      _ = D * B' := by rw [hB'B, Matrix.one_mul]
  have hUS : U * S₁ = S₂ * U := by
    calc U * S₁ = B * (a * D) * B' := by simp only [U, Matrix.mul_assoc, hB'S]
      _ = B * (T * a) * B' := by rw [ha2]
      _ = (B * B') * S₂ * (B * a * B') := by simp only [T, Matrix.mul_assoc]
      _ = S₂ * U := by rw [hBB, Matrix.one_mul]
  refine ⟨U.map star, V.map star, ?_, ?_, ?_⟩
  · have hUV : U * V = 1 := mul_eq_one_comm.1 hVU
    have : (U * V).map star = (1 : Matrix (Fin n) (Fin n) ℂ).map star := by rw [hUV]
    rw [show (1 : Matrix (Fin n) (Fin n) ℂ) = (1 : Matrix (Fin n) (Fin n) ℂ).map star by simp, ← this]; ext i j; simp [Matrix.mul_apply, star_sum]
  · have e : (U.map star)ᵀ = Uᴴ := rfl
    rw [e, show (U.map star).map star = U by ext i j; simp, hUU]
  · have : (U * S₁).map star = (S₂ * U).map star := by rw [hUS]
    have e1 : (U * S₁).map star = U.map star * θ₁ := by ext i j; simp [S₁, Matrix.mul_apply, star_sum]
    have e2 : (S₂ * U).map star = θ₂ * U.map star := by ext i j; simp [S₂, Matrix.mul_apply, star_sum]
    rw [← e1, ← e2, this]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (x : E) : piInf τ (inclR (F := F) (AF F) x) = τ.1 x := by
  simp [piInf, inclR, compInf, infEmb_tmul]


variable (F E) in
def archIdeal : Ideal (AE F E) where
  carrier := {z | At (evI F) z}
  add_mem' := fun {a b} ha hb u hu => by rw [smul_add, ha u hu, hb u hu, add_zero]
  zero_mem' := fun u _ => smul_zero u
  smul_mem' := fun c z hz u hu => by
    rw [smul_eq_mul, ← mul_smul_comm, hz u hu, mul_zero]

theorem cA_mem_archIdeal (σ : E →ₐ[F] E) {z : AE F E} (hz : z ∈ archIdeal F E) : cA σ z ∈ archIdeal F E :=
  fun u hu => by rw [← map_smul, hz u hu, map_zero]

end GlobalTheory.ConjCartan

namespace GlobalTheory.ConjCartan

theorem mapMatrix_transpose {R S : Type} [Semiring R] [Semiring S] (f : R →+* S) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : f.mapMatrix Aᵀ = (f.mapMatrix A)ᵀ := rfl

theorem conj_cartan_arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n r s : ℕ) (X Y : Spc F E n), B.IsGood σ → X.IsHerm σ B r s → (reS X Y).IsHerm σ B r s →
    ∃ g ∈ UAt σ X (evI F), ∀ w, (mat g).map (piInf (B.emb w)) * X.θ w = Y.θ w * (mat g).map (piInf (B.emb w)) := by
  intro F E _ _ _ _ _ σ B n r s X Y hB hX hY
  have cm := hB.cm
  have hM : ∀ w, (X.J.map (B.emb w).1)ᴴ = X.J.map (B.emb w).1 := fun w => by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [← cm.2.2.2 (B.emb w).1, hX.herm]
  have hU := fun w => exists_conj_cartan_matrix n _ (X.θ w) (Y.θ w) (hM w) (hX.cartan w) (hY.cartan w)
  choose u v huv hun hint using hU
  choose lift hlat hlev using GlobalTheory.T.exists_supportedAtInfinity_adele_with_complexComponents F E σ cm B.emb
  let π := Ideal.Quotient.mk (archIdeal F E)
  let Dm : Matrix (Fin n) (Fin n) (AE F E) := Matrix.of fun i j => lift fun w => (u w - 1) i j
  let Dv : Matrix (Fin n) (Fin n) (AE F E) := Matrix.of fun i j => lift fun w => (v w - 1) i j
  have hDm : π.mapMatrix Dm = 0 := by
    ext i j; exact Ideal.Quotient.eq_zero_iff_mem.2 (hlat _)
  have hDv : π.mapMatrix Dv = 0 := by
    ext i j; exact Ideal.Quotient.eq_zero_iff_mem.2 (hlat _)
  have hDc : π.mapMatrix ((cA σ).toRingHom.mapMatrix Dm) = 0 := by
    ext i j; exact Ideal.Quotient.eq_zero_iff_mem.2 (cA_mem_archIdeal σ (hlat _))
  have hDmw : ∀ w, (piInf (B.emb w)).mapMatrix Dm = u w - 1 := fun w => by
    ext i j; exact hlev _ w
  have hDvw : ∀ w, (piInf (B.emb w)).mapMatrix Dv = v w - 1 := fun w => by
    ext i j; exact hlev _ w
  have zero : ∀ Z : Matrix (Fin n) (Fin n) (AE F E), π.mapMatrix Z = 0 → (∀ w, (piInf (B.emb w)).mapMatrix Z = 0) → Z = 0 := by
    intro Z h1 h2; ext i j
    exact GlobalTheory.T.supportedAtInfinity_adele_eq_zero_of_complexComponents F E σ cm B.emb _ (Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (congrFun h1 i) j))
      (fun w => congrFun (congrFun (h2 w) i) j)
  have hGH : (1 + Dm) * (1 + Dv) = 1 := by
    refine sub_eq_zero.1 (zero _ ?_ fun w => ?_)
    · rw [map_sub, map_mul, map_add (f := _), map_add (f := _), map_one, hDm, hDv]; simp
    · rw [map_sub, map_mul, map_add (f := _), map_add (f := _), map_one, hDmw, hDvw, add_sub_cancel, add_sub_cancel, huv w, sub_self]
  let g0 : GL (Fin n) (AE F E) := ⟨1 + Dm, 1 + Dv, hGH, mul_eq_one_comm.1 hGH⟩
  have hcw : ∀ w, (piInf (B.emb w)).mapMatrix ((cA σ).toRingHom.mapMatrix Dm) = (u w).map star - 1 := fun w => by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [show (cA σ).toRingHom (Dm i j) = cA σ (Dm i j) from rfl, GlobalTheory.T.realPlaceComponent_adeleConjugation_eq_complexConj F E σ cm w (B.emb w)]
    simp only [Dm, Matrix.of_apply]
    rw [hlev]
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.map_apply, star_sub]
    split_ifs <;> simp
  have hJw : ∀ w, (piInf (B.emb w)).mapMatrix (incM F X.J) = X.J.map (B.emb w).1 := fun w => by
    ext i j; simp [incM, piInf_inclR]
  have hUG : g0 ∈ UG (cA σ) (incM F X.J) := by
    change (1 + Dm)ᵀ * incM F X.J * (cA σ).toRingHom.mapMatrix (1 + Dm) = incM F X.J
    rw [map_add (f := _), map_one]
    refine sub_eq_zero.1 (zero _ ?_ fun w => ?_)
    · rw [map_sub, map_mul, map_mul, mapMatrix_transpose, map_add (f := _), map_add (f := _), map_one, hDm, hDc]; simp
    · rw [map_sub, map_mul, map_mul, mapMatrix_transpose, map_add (f := _), map_add (f := _), map_one, hDmw, hcw, hJw,
        add_sub_cancel, add_sub_cancel, hun w, sub_self]
  refine ⟨⟨g0, hUG⟩, ?_, fun w => ?_⟩
  · intro a ha
    show a • ((1 + Dm) - 1) = 0
    ext i j
    simp only [add_sub_cancel_left, Matrix.smul_apply, Matrix.zero_apply]
    exact hlat _ a ha
  · have : (mat (⟨g0, hUG⟩ : UA σ X.J)).map (piInf (B.emb w)) = u w := by
      show (piInf (B.emb w)).mapMatrix (1 + Dm) = u w
      rw [map_add (f := _), map_one, hDmw]; abel
    rw [this]; exact hint w

end GlobalTheory.ConjCartan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartGraphCoordinatesOpNormLeOfSmall
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ChartGraph

namespace GlobalTheory.ChartGraph

open Matrix

theorem sum_norm_mulVec_sq_le {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (c : ℝ)
    (h : ∀ i j, ‖M i j‖ ≤ c) (w : Fin n → ℂ) :
    ∑ i, ‖(M *ᵥ w) i‖ ^ 2 ≤ ((m : ℝ) * n * c ^ 2) * ∑ j, ‖w j‖ ^ 2 := by
  have hi : ∀ i, ‖(M *ᵥ w) i‖ ≤ c * ∑ j, ‖w j‖ := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    calc ‖∑ j, M i j * w j‖ ≤ ∑ j, ‖M i j * w j‖ := norm_sum_le _ _
      _ ≤ ∑ j, c * ‖w j‖ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (h i j) (norm_nonneg _)
      _ = c * ∑ j, ‖w j‖ := by rw [Finset.mul_sum]
  have hs : (∑ j, ‖w j‖) ^ 2 ≤ n * ∑ j, ‖w j‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖w j‖)
  have hi2 : ∀ i, ‖(M *ᵥ w) i‖ ^ 2 ≤ c ^ 2 * (n * ∑ j, ‖w j‖ ^ 2) := fun i => by
    calc ‖(M *ᵥ w) i‖ ^ 2 ≤ (c * ∑ j, ‖w j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hi i) 2
      _ = c ^ 2 * (∑ j, ‖w j‖) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (sq_nonneg c)
  calc ∑ i, ‖(M *ᵥ w) i‖ ^ 2 ≤ ∑ _i : Fin m, c ^ 2 * (n * ∑ j, ‖w j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => hi2 i
    _ = _ := by simp [Finset.sum_const]; ring

theorem sqrt_sum_norm_sq_eq {n : ℕ} (x : Fin n → ℂ) :
    Real.sqrt (∑ i, ‖x i‖ ^ 2) = ‖WithLp.toLp 2 x‖ := by
  rw [EuclideanSpace.norm_eq]

theorem norm_toLp_mulVec_le {m n r : ℕ} (hm : m ≤ r) (hn : n ≤ r) (M : Matrix (Fin m) (Fin n) ℂ)
    (c : ℝ) (hc : 0 ≤ c) (h : ∀ i j, ‖M i j‖ ≤ c) (w : Fin n → ℂ) :
    ‖WithLp.toLp 2 (M *ᵥ w)‖ ≤ (r * c) * ‖WithLp.toLp 2 w‖ := by
  rw [← sqrt_sum_norm_sq_eq, ← sqrt_sum_norm_sq_eq]
  have hmn : (m : ℝ) * n * c ^ 2 ≤ ((r : ℝ) * c) ^ 2 := by
    have h1 : (m : ℝ) ≤ r := by exact_mod_cast hm
    have h2 : (n : ℝ) ≤ r := by exact_mod_cast hn
    have : (m : ℝ) * n ≤ (r : ℝ) * r :=
      mul_le_mul h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    nlinarith [sq_nonneg c]
  have hS := sum_norm_mulVec_sq_le M c h w
  have hB : 0 ≤ ∑ j, ‖w j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc Real.sqrt (∑ i, ‖(M *ᵥ w) i‖ ^ 2) ≤ Real.sqrt (((r : ℝ) * c) ^ 2 * ∑ j, ‖w j‖ ^ 2) :=
        Real.sqrt_le_sqrt (hS.trans (mul_le_mul_of_nonneg_right hmn hB))
    _ = (r * c) * Real.sqrt (∑ j, ‖w j‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg _) hc)]

end GlobalTheory.ChartGraph

namespace GlobalTheory.ChartGraph

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem norm_coord_le (X : Data E r) (z : V (nd X)) (k : Fin (nd X)) : ‖z k‖ ≤ ‖z‖ :=
  PiLp.norm_apply_le z k

theorem norm_chartMatrixTopBlock_sub_one_le (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (i j : Fin X.p0) :
    ‖(chartMatrixTopBlock X z τ - 1) i j‖ ≤ ‖z‖ := by
  simp only [chartMatrixTopBlock, Matrix.sub_apply, Matrix.submatrix_apply, mat, Matrix.of_apply, nmat,
    Matrix.one_apply]
  split_ifs
  all_goals first
    | (rw [sub_zero]; exact norm_coord_le X z _)
    | (rw [sub_self, norm_zero]; exact norm_nonneg _)
    | (exfalso; simp only [Fin.lt_def, Fin.ext_iff, Fin.coe_castLE] at *; omega)

theorem norm_chartBottomLeftBlock_le (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (i : Fin (r - X.p0)) (j : Fin X.p0) :
    ‖chartBottomLeftBlock X z τ i j‖ ≤ ‖z‖ := by
  simp only [chartBottomLeftBlock, Matrix.submatrix_apply, mat, Matrix.of_apply, nmat]
  split_ifs with h1 h2
  · exact norm_coord_le X z _
  · exact absurd h2 (by intro h; have := congrArg Fin.val h; simp at this; omega)
  · exact absurd (show Fin.castLE X.p0_le j < ⟨X.p0 + i, by have := i.isLt; have := X.p0_le; omega⟩ from
      by rw [Fin.lt_def]; simp; omega) h1

end GlobalTheory.ChartGraph

namespace GlobalTheory.ChartGraph

open Matrix

theorem zN_graphCoord_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (z : V (nd X)), (r : ℝ) ^ 2 * ‖z‖ ≤ 1 / 100 → X.zN (graphCoord X z) ≤ 1 / 50 := by
  intro E _ _ _ r X z hz
  have hε : 0 ≤ ‖z‖ := norm_nonneg z
  have hrε : (r : ℝ) * ‖z‖ ≤ 1 / 100 := by
    rcases Nat.eq_zero_or_pos r with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ r := by exact_mod_cast h
      nlinarith
  apply Real.iSup_le _ (by norm_num)
  intro τ
  apply Real.sSup_le _ (by norm_num)
  rintro t ⟨v, hv, rfl⟩
  have hunit : IsUnit (chartMatrixTopBlock X z τ).det := by rw [chartMatrixTopBlock_det_eq_one]; exact isUnit_one
  have hAv : Matrix.of (graphCoord X z τ) *ᵥ v = chartBottomLeftBlock X z τ *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v) := by
    change (chartBottomLeftBlock X z τ * (chartMatrixTopBlock X z τ)⁻¹) *ᵥ v = _
    exact (Matrix.mulVec_mulVec _ _ _).symm
  have hvw : v = (chartMatrixTopBlock X z τ)⁻¹ *ᵥ v + (chartMatrixTopBlock X z τ - 1) *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
      Matrix.one_mulVec]
    abel
  have h1 := norm_toLp_mulVec_le (Nat.sub_le r X.p0) X.p0_le (chartBottomLeftBlock X z τ) ‖z‖ hε
    (norm_chartBottomLeftBlock_le X z τ) ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)
  have h2 := norm_toLp_mulVec_le X.p0_le X.p0_le (chartMatrixTopBlock X z τ - 1) ‖z‖ hε
    (norm_chartMatrixTopBlock_sub_one_le X z τ) ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)
  have h3 : ‖WithLp.toLp 2 ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)‖ ≤ ‖WithLp.toLp 2 v‖ +
      ‖WithLp.toLp 2 ((chartMatrixTopBlock X z τ - 1) *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v))‖ := by
    have hv' : WithLp.toLp 2 v = WithLp.toLp 2 ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v) +
        WithLp.toLp 2 ((chartMatrixTopBlock X z τ - 1) *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)) := by
      rw [← WithLp.toLp_add, ← hvw]
    have : WithLp.toLp 2 ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v) = WithLp.toLp 2 v -
        WithLp.toLp 2 ((chartMatrixTopBlock X z τ - 1) *ᵥ ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v)) := by
      rw [hv', add_sub_cancel_right]
    rw [this]
    exact norm_sub_le _ _
  have hvpos : 0 < ‖WithLp.toLp 2 v‖ :=
    norm_pos_iff.mpr fun h => hv (by simpa using congrArg WithLp.ofLp h)
  rw [sqrt_sum_norm_sq_eq, sqrt_sum_norm_sq_eq, hAv, div_le_iff₀ hvpos]
  have hb := norm_nonneg (WithLp.toLp 2 ((chartMatrixTopBlock X z τ)⁻¹ *ᵥ v))
  have h4 := mul_le_mul_of_nonneg_right hrε hb
  linarith

end GlobalTheory.ChartGraph
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormOfGramMatrixAtHolomorphicFrameChange
section
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.CxForm

theorem chernAt_changeFrame : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H K A : V n → Matrix r r ℂ) (v : V n), MContDiffAt 2 K v → IsUnit (K v).det → (∀ i j, AnalyticAt ℂ (fun w => A w i j) v) → IsUnit (A v).det → (H =ᶠ[𝓝 v] fun w => chg (A w) (K w)) → ∀ j, chernAt H v j = chernAt K v j := by
  intro n r _ _ H K A v hK hKu hg hAu hH j
  have hconj : ∀ (M P Q : Matrix r r (MvPolynomial (Fin n × Fin n) ℂ)), Q * P = 1 →
      (Q * M * P).charpolyRev = M.charpolyRev := by
    intro M P Q hQP
    have hQP' : Q.map Polynomial.C * P.map Polynomial.C = 1 := by
      rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
    have e : (1 : Matrix r r (Polynomial (MvPolynomial (Fin n × Fin n) ℂ))) -
        (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) ℂ)) • (Q * M * P).map Polynomial.C =
        Q.map Polynomial.C * (1 - (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) ℂ)) •
          M.map Polynomial.C) * P.map Polynomial.C := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hQP',
        Matrix.mul_smul, Matrix.smul_mul]
    rw [Matrix.charpolyRev, Matrix.charpolyRev, e, Matrix.det_mul, Matrix.det_mul, mul_right_comm,
      ← Matrix.det_mul, hQP', Matrix.det_one, one_mul]
  have hsum : ∀ G : V n → Matrix r r ℂ, curvPoly G v =
      ∑ a, ∑ b, (MvPolynomial.X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) •
        (curv G v (coordVec a) (coordVec b)).map MvPolynomial.C := by
    intro G
    ext i j
    simp [curvPoly, Matrix.sum_apply, mul_comm]
  have hA : MContDiffAt 2 A v := fun a b => (hg a b).contDiffAt.restrict_scalars ℝ
  have hA0 : ∀ᶠ x in 𝓝 v, ∀ η, mdbar A x η = 0 := by
    have hev : ∀ᶠ x in 𝓝 v, ∀ a b, AnalyticAt ℂ (fun w => A w a b) x :=
      eventually_all.2 fun a => eventually_all.2 fun b => (hg a b).eventually_analyticAt
    filter_upwards [hev] with x hx η
    ext a b
    rw [mdbar_apply, GlobalTheory.dbar_eq_zero (hx a b).differentiableAt]
    rfl
  have hGe : H =ᶠ[𝓝 v] fun u => (A u)ᵀ * K u * (A u)ᴴᵀ := hH
  have hcurv : ∀ ξ η, curv H v ξ η = (A v)⁻¹ * curv K v ξ η * A v :=
    fun ξ η => by rw [curv_congr hGe, curv_changeFrame hK hKu hA hAu hA0]
  have key : curvPoly H v = ((A v)⁻¹).map MvPolynomial.C * curvPoly K v * (A v).map MvPolynomial.C := by
    rw [hsum, hsum]
    simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul, hcurv]
  have key2 : chernPoly H v j = chernPoly K v j := by
    rw [chernPoly, chernPoly, key, show ∀ (Q M P : Matrix r r (MvPolynomial (Fin n × Fin n) ℂ)),
      -(Q * M * P) = Q * (-M) * P from fun Q M P => by rw [Matrix.mul_neg, Matrix.neg_mul], hconj]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hAu, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [chernAt, chernAt, key2]

end GlobalTheory.CxForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEqMapDomain
section
noncomputable section

open Formalism.BasicNotions

namespace GlobalTheory.GoodIdemTie

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.factPrime

theorem idemTie_of_tameTie (hG : GlobalTheory.Published.GreenCuspidal) (D : D7) (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ)
    (hT : GlobalTheory.DimPartsCompare.TameTie D om) : GlobalTheory.DimPartsCompare.IdemTie D om :=
  hT.idemTie hG.green

end GlobalTheory.GoodIdemTie

end
end

