module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupFiniteDimensionalRepContainsHighestW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.APlusComm
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.Bundle0001
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAt
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.Branching

noncomputable section

namespace GlobalTheory.DefU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def infSpan (φ : UA E n → ℂ) : Submodule ℂ (UA E n → ℂ) :=
  Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)

theorem RU_mem_infSpan (φ : UA E n → ℂ) {x : UA E n} (hx : x ∈ infU E n) {ψ : UA E n → ℂ} (hψ : ψ ∈ infSpan φ) :
    RU E n x ψ ∈ infSpan φ := by
  have : infSpan φ ≤ (infSpan φ).comap (RU E n x) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    show RU E n x (RU E n k φ) ∈ infSpan φ
    rw [RU_RU]
    exact Submodule.subset_span ⟨⟨x * k, mul_mem hx k.2⟩, rfl⟩
  exact this hψ

theorem mem_infU_of_mem_embU {τ : E →+* ℂ} {x : UA E n} (hx : x ∈ embU n τ) : x ∈ infU E n :=
  (Subgroup.mem_inf.1 hx).1

theorem exists_hasWeightAt (U : AutSub E n) (τ : E →+* ℂ) : ∃ lam, HasWeightAt U.V τ lam := by
  obtain ⟨e, he⟩ := _root_.GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n τ
  obtain ⟨φ, hφU, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot U.isAut.ne_bot
  let j : Matrix.unitaryGroup (Fin n) ℂ →* UA E n := (embU n τ).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have hj : ∀ u, j u ∈ infU E n := fun u => mem_infU_of_mem_embU (e.symm u).2
  let S := infSpan φ
  have hφS : φ ∈ S := by
    have : RU E n (1 : infU E n) φ ∈ S := Submodule.subset_span ⟨1, rfl⟩
    simpa using this
  have hS : S ≤ U.V := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact U.isAut.stable _ _ hφU)
  haveI : FiniteDimensional ℂ S := (U.isAut.aut φ hφU).kfin
  haveI : Nontrivial S := ⟨⟨⟨φ, hφS⟩, 0, fun h => hφ0 (congrArg Subtype.val h)⟩⟩
  let ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) S :=
    sub ((RU E n).comp j) S (fun u ψ hψ => RU_mem_infSpan φ (hj u) hψ)
  have hρ : ∀ u (v : S), (ρ u v : UA E n → ℂ) = RU E n (j u) v := fun _ _ => rfl
  have hcont : ∀ (l : Module.Dual ℂ S) (v : S), Continuous fun u => l (ρ u v) := by
    let P : Submodule ℂ (Module.Dual ℂ S) :=
      { carrier := {l | ∀ v : S, Continuous fun u => l (ρ u v)}
        add_mem' := fun ha hb v => (ha v).add (hb v)
        zero_mem' := fun _ => continuous_const
        smul_mem' := fun c _ ha v => (ha v).const_smul c }
    have hev : ∀ g : UA E n, (LinearMap.proj g ∘ₗ S.subtype : Module.Dual ℂ S) ∈ P := fun g v => by
      have hv : Continuous (v : UA E n → ℂ) := (U.isAut.aut _ (hS v.2)).cont
      have : Continuous fun u => (j u : UA E n) := continuous_subtype_val.comp e.symm.continuous
      exact hv.comp ((continuous_const_mul g).comp this)
    have h1 : P.dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext (funext fun g => hv _ (hev g)))
    have hP : P = ⊤ := by
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := P), h1, Submodule.dualAnnihilator_bot]
    intro l v
    have : l ∈ P := hP ▸ Submodule.mem_top
    exact this v
  obtain ⟨lam, f, hf⟩ := _root_.GlobalTheory.UnitaryContainsType.exists_smallRep_intertwining n S ρ hcont
  refine ⟨lam, isIrreducible_smallRep_id n lam, S.subtype ∘ₗ f.toLinearMap, fun h0 => hf ?_,
    fun v => hS (f v).2, fun x v => ?_⟩
  · refine Representation.IntertwiningMap.ext (LinearMap.ext fun v => Subtype.ext ?_)
    simpa using LinearMap.congr_fun h0 v
  · have h1 : ((cEmb τ).comp (embU n τ).subtype) x = unitaryIncl n (e x) := (he x).symm
    rw [h1]
    have h2 := Representation.IntertwiningMap.isIntertwining _ _ f (e x) v
    change (f (smallRep (unitaryIncl n) lam (e x) v)).1 = _
    rw [h2, hρ]
    change RU E n ((e.symm (e x) : embU n τ) : UA E n) (f v).1 = _
    rw [e.symm_apply_apply]
    rfl

theorem hasWeightAt_unique (U : AutSub E n) (τ : E →+* ℂ) {lam lam' : DomWeight n} (h : HasWeightAt U.V τ lam)
    (h' : HasWeightAt U.V τ lam') : lam = lam' := by
  obtain ⟨e, he⟩ := _root_.GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n τ
  obtain ⟨r, -, hr1, hr⟩ := _root_.GlobalTheory.DefU.exists_embRet E n τ
  let s : Matrix.unitaryGroup (Fin n) ℂ →* UA E n := (embU n τ).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have mk : ∀ mu, HasWeightAt U.V τ mu →
      ∃ f : (smallRep (unitaryIncl n) mu).IntertwiningMap (U.rep.comp s), f ≠ 0 := by
    rintro mu ⟨-, F, hF0, hFm, hFi⟩
    refine ⟨⟨F.codRestrict U.V hFm, fun u => ?_⟩, fun h0 => hF0 ?_⟩
    · ext v : 1
      apply Subtype.ext
      show F (sqRep ℂ n mu (unitaryIncl n u) v) = RU E n (s u) (F v)
      have : unitaryIncl n u = ((cEmb τ).comp (embU n τ).subtype) (e.symm u) := by
        have h3 := he (e.symm u)
        rw [e.apply_symm_apply] at h3
        exact h3
      rw [this, hFi]
      rfl
    · ext v : 1
      exact congrArg Subtype.val (DFunLike.congr_fun h0 v :)
  obtain ⟨f, hf⟩ := mk lam h
  obtain ⟨f', hf'⟩ := mk lam' h'
  have hc : ∀ g, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y) := fun g =>
    ⟨e (r g), fun y => by
      change Commute ((((e.symm (e (r g))) : embU n τ) : UA E n)⁻¹ * g) ((e.symm y : embU n τ) : UA E n)
      rw [e.symm_apply_apply]
      exact hr g _⟩
  obtain ⟨ee⟩ := (_root_.GlobalTheory.CuspRep.CompUniq.isotypic _ _ _ _ _ U.rep s _ _ U.isIrreducible_rep (isIrreducible_smallRep_unitary n lam)
    (isIrreducible_smallRep_unitary n lam') hc f hf).2 f' hf'
  by_contra hne
  have h0 := intertwining_unitary_eq_zero n lam lam' hne ee.toIntertwiningMap
  obtain ⟨v, hv⟩ := exists_ne (0 : nablaSq ℂ n lam)
  exact hv (ee.injective ((DFunLike.congr_fun h0 v).trans (map_zero ee).symm))

theorem AU.existsUnique_hasWt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AU E n)
    (τ : E →+* ℂ), ∃! lam : DomWeight n, π.HasWt τ lam := by
  intro E _ _ _ n π τ
  obtain ⟨U, rfl⟩ := AU.mk_surjective π
  obtain ⟨lam, h⟩ := exists_hasWeightAt U τ
  exact ⟨lam, h, fun mu hmu => (hasWeightAt_unique U τ h hmu).symm⟩

end GlobalTheory.DefU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalOfBoundedKorbitDimension
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.admitted

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem isKFin_of_mem_closure (hσ : IsURepOn (UJset ε) σ) {U : Set H} {M : ℕ}
    (hU : ∀ u ∈ U, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ M ∧ u ∈ S ∧ IsKStableOn ε σ S)
    {u : H} (hu : u ∈ closure U) : IsKFin ε σ u := by
  let t : Set H := Set.range fun k : KG ε => σ (toMK k) u
  obtain ⟨b, hbt, hsp, hli⟩ := exists_linearIndependent ℂ t
  have hfin : b.Finite := by
    by_contra hinf
    haveI : Infinite b := Set.infinite_coe_iff.2 hinf
    let e : Fin (M + 1) ↪ b := Fin.valEmbedding.trans (Infinite.natEmbedding b)
    choose k hk using fun i => hbt (e i).2
    have hc : Continuous fun w : H => fun i : Fin (M + 1) => σ (toMK (k i)) w :=
      continuous_pi fun i => (σ _).continuous
    have ho := (isOpen_setOf_linearIndependent (𝕜 := ℂ) (E := H) (ι := Fin (M + 1))).preimage hc
    have hu' : LinearIndependent ℂ fun i : Fin (M + 1) => σ (toMK (k i)) u := by
      have := hli.comp e e.injective
      rwa [show (Subtype.val ∘ e : Fin (M + 1) → H) = _ from funext fun i => (hk i).symm] at this
    obtain ⟨w, hw, hwU⟩ := mem_closure_iff.1 hu _ ho hu'
    obtain ⟨S, hS, hM, hwS, hK⟩ := hU w hwU
    have h1 : LinearIndependent ℂ fun i : Fin (M + 1) =>
        (⟨σ (toMK (k i)) w, hK _ (toMK_mem_K _) w hwS⟩ : S) :=
      LinearIndependent.of_comp S.subtype hw
    have h2 := h1.fintype_card_le_finrank
    rw [Fintype.card_fin] at h2
    omega
  refine ⟨Submodule.span ℂ t, hsp ▸ FiniteDimensional.span_of_finite ℂ hfin, Submodule.subset_span ⟨1, ?_⟩,
    fun g hg v hv => ?_⟩
  · exact sigma_one hσ u
  · refine (Submodule.map_span_le (σ g : H →ₗ[ℂ] H) _ _).2 ?_ ⟨v, hv, rfl⟩
    rintro _ ⟨k, rfl⟩
    obtain ⟨g', rfl⟩ : g ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hg
    exact Submodule.subset_span ⟨g' * k, sigma_mul hσ (K_le_UJ hg) (K_le_UJ (toMK_mem_K k)) u⟩

variable [CompleteSpace H]

theorem exists_word_clm (h : Std ε σ) (W : Submodule ℂ H) [CompleteSpace W] (hW : ∀ w ∈ W, Sm ε σ w)
    {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) : ∃ A : W →L[ℂ] H, ∀ w : W, A w = Dw σ l w := by
  obtain ⟨L, hL⟩ := exists_word (isUnit_Jm ε) h.1 l hl
  let A : W →ₗ[ℂ] H := (smooth (Jm ε) σ).subtype ∘ₗ L ∘ₗ Submodule.inclusion hW
  have hA : ∀ x : W, A x = Dw σ l x := fun x => hL _
  refine ⟨⟨A, A.continuous_of_seq_closed_graph fun s x z hs hz =>
    h.dense_smooth.eq_of_inner_right ℂ fun y hy => ?_⟩, hA⟩
  have h1 : Tendsto (fun j => ⟪y, A (s j)⟫_ℂ) atTop (𝓝 ⟪y, z⟫_ℂ) := tendsto_const_nhds.inner hz
  simp only [hA, fun x : W => inner_Dw h.1 hl hy (hW _ x.2)] at h1 ⊢
  exact tendsto_nhds_unique h1
    (tendsto_const_nhds.mul (tendsto_const_nhds.inner ((continuous_subtype_val.tendsto x).comp hs)))

theorem finiteDimensional_of_smooth (h : Std ε σ) (W : Submodule ℂ H) [CompleteSpace W]
    (hW : ∀ w ∈ W, Sm ε σ w) : FiniteDimensional ℂ W := by
  obtain ⟨S, C, hS, hC, hts⟩ := _root_.GlobalTheory.TypeSum.SobHS.sobolev_hilbertSchmidt n ε H σ h
  choose A hA using fun l : {l // l ∈ S} => exists_word_clm h W hW (hS l.1 l.2)
  haveI : Finite {l // l ∈ S} := (List.finite_toSet S).to_subtype
  obtain ⟨B, hB⟩ := (Set.finite_range fun l => ‖A l‖ ^ 2).bddAbove
  have hB' : ∀ l, ‖A l‖ ^ 2 ≤ |B| := fun l => (hB ⟨l, rfl⟩).trans (le_abs_self B)
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ W
  have hfin : Finite w := by
    by_contra hinf
    haveI : Infinite w := not_finite_iff_infinite.1 hinf
    obtain ⟨m, hm⟩ := exists_nat_gt (C * |B|)
    let e : Fin m ↪ w := Fin.valEmbedding.trans (Infinite.natEmbedding w)
    have ho : Orthonormal ℂ fun j => b (e j) := b.orthonormal.comp e e.injective
    have key := hts (Fin m) (fun j => b (e j)) (fun j => b (e j)) |B| (abs_nonneg B) (fun j => hW _ (b (e j)).2)
      (fun l hl z => by
        have e1 : ∑ j, z j • Dw σ l (b (e j) : H) = A ⟨l, hl⟩ (∑ j, z j • b (e j)) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hA]
        have e2 : ‖∑ j, z j • b (e j)‖ ^ 2 = ∑ j, ‖z j‖ ^ 2 := by
          have := ho.inner_sum z z Finset.univ
          rw [inner_self_eq_norm_sq_to_K] at this
          simp only [RCLike.conj_mul] at this
          exact_mod_cast this
        rw [e1, ← e2]
        calc _ ≤ (‖A ⟨l, hl⟩‖ * ‖∑ j, z j • b (e j)‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) ((A _).le_opNorm _) 2
          _ ≤ _ := by rw [mul_pow]; exact mul_le_mul_of_nonneg_right (hB' _) (sq_nonneg _))
    have hn : ∀ j, ‖(b (e j) : H)‖ = 1 := fun j => ho.1 j
    simp only [inner_self_eq_norm_sq_to_K, hn] at key
    simp at key
    have h0 : 0 ≤ C * |B| := mul_nonneg hC (abs_nonneg B)
    nlinarith
  haveI := Fintype.ofFinite w
  exact b.toOrthonormalBasis.toBasis.finiteDimensional_of_finite

end GlobalTheory.TypeSum.admitted

namespace GlobalTheory.TypeSum

theorem finiteDimensional_of_bounded_orbits : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (U : Submodule ℂ H) (M : ℕ),
    (∀ u ∈ U, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ M ∧ u ∈ S ∧ IsKStableOn ε σ S) →
      FiniteDimensional ℂ U := by
  intro n ε H _ _ _ σ h U M hU
  haveI : CompleteSpace U.topologicalClosure := U.isClosed_topologicalClosure.completeSpace_coe
  haveI := admitted.finiteDimensional_of_smooth h U.topologicalClosure fun w hw =>
    h.2.2.1 w (admitted.isKFin_of_mem_closure h.1 (U := U) hU hw)
  exact Submodule.finiteDimensional_of_le U.le_topologicalClosure

end GlobalTheory.TypeSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorChangeOrthonormalBasesSubst
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockBasis

section Mat

variable {m n : ℕ}

theorem unitMap_mul (B u : Matrix (Fin n) (Fin n) ℂ) (B' k : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) (j : Fin n) :
    Formalism.IndefR.Datum.unitMap (B * u) (B' * k) i j =
      ∑ a, ∑ b, (k a i * u⁻¹ j b) • Formalism.IndefR.Datum.unitMap B B' a b := by
  have e : k * Matrix.single i j (1 : ℂ) * u⁻¹ = ∑ a, ∑ b, (k a i * u⁻¹ j b) • Matrix.single a b (1 : ℂ) := by
    rw [Matrix.matrix_eq_sum_single (k * Matrix.single i j (1 : ℂ) * u⁻¹)]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
    congr 1
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · simp
    · intro c _ hc
      simp [Matrix.mul_single_apply_of_ne _ _ _ _ _ hc]
    · simp
  unfold Formalism.IndefR.Datum.unitMap
  rw [Matrix.mul_inv_rev]
  calc B' * k * Matrix.single i j (1 : ℂ) * (u⁻¹ * B⁻¹) = B' * (k * Matrix.single i j (1 : ℂ) * u⁻¹) * B⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [e]
        simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]


open scoped ComplexOrder in
theorem isCartanInv_one {G B : Matrix (Fin n) (Fin n) ℂ} (hB : Bᴴ * G * B = 1) : IsCartanInv G 1 := by
  have hu : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hB
  have h1 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, conjTranspose_one]
  have hG : G = (B⁻¹)ᴴ * 1 * B⁻¹ := by
    rw [← hB, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hu]
  refine ⟨Matrix.one_mul _, by simp, ?_⟩
  rw [Matrix.mul_one, hG]
  refine Matrix.PosDef.conjTranspose_mul_mul_same Matrix.PosDef.one ?_
  exact Matrix.mulVec_injective_iff_isUnit.2 (Matrix.isUnit_nonsing_inv_iff.2 ((Matrix.isUnit_iff_isUnit_det _).2 hu))

end Mat

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (s : Matrix (Fin T.rank) (Fin T.rank) ℂ)
  {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
include hψ hθ hf

theorem aPlus_add_dir (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (z + z') f =
      Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) z f + Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) z' f := by
  have e : cplxO 1 s (z + z') = cplxO 1 s z + cplxO 1 s z' := by
    simp only [cplxO, Matrix.mul_add, Matrix.add_mul, smul_add]
  simp only [GlobalTheory.FockSubst.aPlus_eq, e, fun z => (GlobalTheory.FockSubst.dRho_laws hψ hθ hf τ z).2.2.1]
  module

theorem dRho_smul_dir (c : ℂ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Datum.dRho (heisO ψ S T) θ τ (c • z) f =
      (c.re : ℂ) • Datum.dRho (heisO ψ S T) θ τ z f + (c.im : ℂ) • Datum.dRho (heisO ψ S T) θ τ (Complex.I • z) f := by
  have e : c • z = (c.re : ℂ) • z + (c.im : ℂ) • (Complex.I • z) := by
    rw [smul_smul, ← add_smul, Complex.re_add_im]
  rw [e, (GlobalTheory.FockSubst.dRho_laws hψ hθ hf τ _).2.2.1, (GlobalTheory.FockSubst.dRho_laws hψ hθ hf τ _).2.2.2.1,
    (GlobalTheory.FockSubst.dRho_laws hψ hθ hf τ _).2.2.2.1]

theorem aPlus_smul_dir (e : Bool) (c : ℂ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (hz : cplxO 1 s z = (Complex.I * if e then 1 else -1) • z) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (c • z) f =
      (if e then c else star c) • Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) z f := by
  have e1 : cplxO 1 s (c • z) = c • cplxO 1 s z := by
    simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul, smul_comm c]
  simp only [GlobalTheory.FockSubst.aPlus_eq]
  rw [e1, hz, smul_smul, dRho_smul_dir hψ hθ τ hf c, dRho_smul_dir hψ hθ τ hf (c * _),
    dRho_smul_dir hψ hθ τ hf (Complex.I * _)]
  generalize ((fockScale D τ : ℝ) : ℂ)⁻¹ = r
  cases e
  · match_scalars <;> apply Complex.ext <;> simp <;> ring
  · match_scalars <;> apply Complex.ext <;> simp <;> ring

theorem aPlus_sum_dir {ι : Type} (t : Finset ι) (z : ι → Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (∑ i ∈ t, z i) f =
      ∑ i ∈ t, Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (z i) f := by
  induction t using Finset.induction_on with
  | empty =>
    have h := aPlus_add_dir hψ hθ τ s hf 0 0
    rw [add_zero] at h
    rw [Finset.sum_empty, Finset.sum_empty]
    exact left_eq_add.1 h
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, aPlus_add_dir hψ hθ τ s hf, ih]

theorem aPlus_unitMap_mul {ε : Fin T.rank → Bool} {B' k : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (ht : s * B' = B' * diagonal fun a => if ε a then (1 : ℂ) else -1) (hk : k ∈ Formalism.REAL.Kset ε)
    (B : Matrix (Fin S.rank) (Fin S.rank) ℂ) {u : Matrix (Fin S.rank) (Fin S.rank) ℂ}
    (hu : u ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) (i : Fin T.rank) (j : Fin S.rank) :
    Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (Formalism.IndefR.Datum.unitMap (B * u) (B' * k) i j) f =
      ∑ a, ∑ b, (if ε i = true then k a i * u⁻¹ j b else k⁻¹ i a * u b j) •
        Datum.aPlus (heisO ψ S T) θ τ (cplxO 1 s) (Formalism.IndefR.Datum.unitMap B B' a b) f := by
  rw [unitMap_mul, aPlus_sum_dir hψ hθ τ _ hf]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [aPlus_sum_dir hψ hθ τ _ hf]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [aPlus_smul_dir hψ hθ τ _ hf (ε a) _ _ (GlobalTheory.FockIndep.cplxO_unitMap ht a b)]
  refine congrArg (· • _) ?_
  have hk1 : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hk.1)
  have hu1 : u⁻¹ = uᴴ := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 hu)
  have hc := congrFun (congrFun hk.2 a) i
  rw [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at hc
  rw [hk1, hu1, Matrix.conjTranspose_apply, Matrix.conjTranspose_apply, star_mul', star_star]
  by_cases h : ε a = ε i
  · rw [h]
  · have h0 : k a i = 0 := by
      cases h1 : ε a <;> cases h2 : ε i <;> simp only [h1, h2, not_true, if_true, Bool.false_eq_true, if_false] at h hc
      · linear_combination hc / 2
      · linear_combination -hc / 2
    simp [h0]

omit hψ hθ hf

section Generic

variable {ι κ μ X : Type} [Fintype κ] [Fintype μ] {A A' : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}

theorem pure_subst {g : X → ℂ} (c : ι → κ → μ → ℂ) (e : ι → κ → μ → ι)
    (hm : ∀ Q, P (pureTensorL A g Q))
    (hX : ∀ v Q, pureTensorL A g (MvPolynomial.X v * Q) = A v (pureTensorL A g Q))
    (hX' : ∀ v Q, pureTensorL A' g (MvPolynomial.X v * Q) = A' v (pureTensorL A' g Q))
    (hA : ∀ v h, P h → A' v h = ∑ a, ∑ b, c v a b • A (e v a b) h) (Q : MvPolynomial ι ℂ) :
    pureTensorL A' g Q = pureTensorL A g
      (MvPolynomial.aeval (fun v => ∑ a, ∑ b, MvPolynomial.C (c v a b) * MvPolynomial.X (e v a b)) Q) := by
  have hC : ∀ (A : ι → (X → ℂ) → (X → ℂ)) a, pureTensorL A g (MvPolynomial.C a) = a • g := fun A a => by
    rw [← mul_one (MvPolynomial.C a), MvPolynomial.C_mul', map_smul, GlobalTheory.FockIndep.pure_one]
  induction Q using MvPolynomial.induction_on with
  | C a => rw [hC, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, hC]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [mul_comm, hX', hp, map_mul, MvPolynomial.aeval_X, hA _ _ (hm _)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_mul, map_sum, mul_assoc]
    simp only [MvPolynomial.C_mul', map_smul, smul_mul_assoc, hX]

end Generic

theorem pureTensorO_basis : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → ∀ (k : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (u : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ τ, k τ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ, u τ ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) → ∀ f, IsThetaFunO ψ S T f → ∀ P : PolF D T.rank S.rank, pureTensorO ψ θ S T (fun _ => 1) (cart M) (fun τ => BS τ * u τ) (fun τ => onb M τ * k τ) f P = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (fsub M.ε k u P) := by
  intro D ψ θ S T Sp M BS hψ hθ hB k u hk hu f hf P
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hS := fun τ => isCartanInv_one (hB τ)
  have hfr := fun τ => (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have ht : ∀ τ, cart M τ * onb M τ = onb M τ * diagonal fun a => if M.ε τ a then (1 : ℂ) else -1 := fun τ => by
    rw [cart, onb, Matrix.mul_nonsing_inv_cancel_right _ _ (hfr τ)]
    rfl
  have hadd : ∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → IsThetaFunO ψ S T (g + g') :=
    fun _ _ => GlobalTheory.OrientedHeis.theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (a • g) :=
    fun a _ => GlobalTheory.OrientedHeis.theta_smul a
  have hth : ∀ B B' v g, IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) B B' v g) :=
    fun _ _ _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h
  have hX : ∀ B B' v Q,
      pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) B B') f (MvPolynomial.X v * Q) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) B B' v
        (pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) B B') f Q) := fun B B' v Q => by
    refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) hadd hsm (hth B B') ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' (sS := fun _ => 1) hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  have hA : ∀ v g, IsThetaFunO ψ S T g →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) (fun τ => BS τ * u τ) (fun τ => onb M τ * k τ) v g =
      ∑ a, ∑ b, (if M.ε v.1 v.2.1 = true then k v.1 a v.2.1 * (u v.1)⁻¹ v.2.2 b
        else (k v.1)⁻¹ v.2.1 a * u v.1 b v.2.2) •
        aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS (onb M) (v.1, a, b) g := fun v g hg => by
    unfold aPlusAll
    exact aPlus_unitMap_mul hψ hθ v.1 _ hg (ht v.1) (hk v.1) _ (hu v.1) v.2.1 v.2.2
  have key := pure_subst (P := IsThetaFunO ψ S T) _ _
    (GlobalTheory.FockIndep.pure_mem (P := IsThetaFunO ψ S T) hadd hsm (hth _ _) hf) (hX _ _) (hX _ _) hA P
  unfold pureTensorO fsub
  exact key

end GlobalTheory.FockBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsModelHolomorphicIntegralExtremalWeight
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLift

theorem holShape_fixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_order → ∀ i, HolShape (R.MW i (sg0 D A)) ∧ ∃ w, WtIs (R.MW i (sg0 D A)) w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R ho i
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hpq : ∀ τ, ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 = (Wc D i).rank :=
    fun τ => GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW i τ
  have hc : ∀ ρ, Formalism.QuantumDeterminants.IsHCParam ((R.MW i (sg0 D A)).lam ρ) := fun ρ => by
    have he := (R.MW i (sg0 D A)).enum ρ
    refine ⟨he.1, fun a => ?_⟩
    obtain ⟨-, f, hf, hS⟩ := he
    have hp : Links.parAt (Wc D i) (sg0 D A) ρ = Formalism.L2.NTheta.holPar _ _ (Formalism.L2.NTheta.wtOf D (Wc D i) ρ) := by
      rw [hs]; exact GlobalTheory.ThetaFiresProbe.parAt_fixed _ ρ
    rw [hp] at hS
    have hm : (f a, (R.MW i (sg0 D A)).ε ρ a) ∈ Formalism.L2.NTheta.holPar _ _ (Formalism.L2.NTheta.wtOf D (Wc D i) ρ) := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hm
    have hx1 := congrArg Prod.fst hx
    have hn : (((Wc D i).rank : ℕ) : ℝ) = (((Wc D i).sig (tauE D ρ)).1 : ℝ) + ((Wc D i).sig (tauE D ρ)).2 := by
      rw [← hpq ρ]; push_cast; rfl
    dsimp only at hx1
    rw [hf a, ← hx1, hn]
    rcases x with c | c
    · refine ⟨Formalism.L2.NTheta.wtOf D (Wc D i) ρ (Sum.inl c) - ((Wc D i).sig (tauE D ρ)).2 - (c : ℕ), ?_⟩
      simp only [Formalism.L2.NTheta.holEnt, Sum.elim_inl]
      push_cast
      ring
    · refine ⟨Formalism.L2.NTheta.wtOf D (Wc D i) ρ (Sum.inr c) - (c : ℕ), ?_⟩
      simp only [Formalism.L2.NTheta.holEnt, Sum.elim_inr]
      push_cast
      ring
  refine ⟨fun ρ => ⟨hc ρ, _, (Nat.le_add_right _ _).trans (hpq ρ).le, fun a => ho i ρ a⟩, ?_⟩
  choose w hw using fun ρ a => Formalism.QuantumDeterminants.low_k_integrable_holds _ ((R.MW i (sg0 D A)).ε ρ) _ (hc ρ).2 a
  exact ⟨fun ρ c => w ρ (revNeg ((R.MW i (sg0 D A)).ε ρ) (arr (nNeg ((R.MW i (sg0 D A)).ε ρ)) c)),
    fun ρ c => (hw ρ _).symm⟩

end GlobalTheory.DefLift
end

