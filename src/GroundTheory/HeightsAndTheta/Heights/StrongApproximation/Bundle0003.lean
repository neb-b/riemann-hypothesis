module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.StrongApproximation.POrthProjection
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem sigA_inclA_apply {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E)
    (x : E) : sigA c (inclA F E x) = inclA F E (c x) := by
  simp [sigA, inclA, Algebra.TensorProduct.map_tmul]

theorem OrthProjection.proof (hT : AETopologicalRing.Statement) : OrthProjection.Statement := by
  refine ⟨?_, ?_⟩
  · intro R _ σ hσ N J hJ e f hee hff hef
    have hfe : hf σ J f e = 1 := by rw [← hf_symm hσ hJ, hef, map_one]
    have perp : ∀ u, hf σ J (perpProj σ J e f u) e = 0 ∧ hf σ J (perpProj σ J e f u) f = 0 := by
      intro u
      simp only [perpProj, hf_sub_left, hf_smul_left, hee, hff, hef, hfe]
      constructor <;> ring
    have fix : ∀ u, hf σ J u e = 0 → hf σ J u f = 0 → perpProj σ J e f u = u := by
      intro u h1 h2
      simp [perpProj, h1, h2]
    refine ⟨⟨fun u v => ?_, fun a u => ?_⟩, fun u => fix _ (perp u).1 (perp u).2, perp, fix⟩
    · simp only [perpProj, hf_add_left, add_smul]
      abel
    · simp only [perpProj, hf_smul_left, smul_sub, mul_smul]
  · intro F E _ _ _ _ _ c h2 hc N J e f _ _
    have := (hT F E c h2 hc).1
    refine ⟨?_, fun u => ?_⟩
    · unfold perpProj hf
      fun_prop
    · have hmap : ∀ x y : Fin N → E, inclA F E (hf c.toRingHom J x y) =
          hf (sigA c) (J.map (inclA F E)) (inclA F E ∘ x) (inclA F E ∘ y) := by
        intro x y
        set_option synthInstance.maxHeartbeats 100000 in
          simp [hf, map_sum, map_mul, sigA_inclA_apply]
      funext i
      simp only [perpProj, Function.comp_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub,
        map_mul, hmap]

end GroundTheory.Heights₂.Heights.StrongApprox
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PPlaceMaps
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA

namespace PlaceMaps

section Lemmas

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]


open Classical in
theorem evalAt_singleF_self (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    evalAt F v (singleF F v x) = x := by
  show Pi.single v x v = x
  simp


open Classical in
theorem evalAt_singleF_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (x : v.adicCompletion F) :
    evalAt F w (singleF F v x) = 0 := by
  show Pi.single v x w = 0
  simp [h]


open Classical in
theorem singleF_mul (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletion F) :
    singleF F v (x * y) = singleF F v x * singleF F v y := by
  apply FiniteAdeleRing.ext; intro w
  change Pi.single v (x * y) w = Pi.single v x w * Pi.single v y w
  by_cases h : w = v
  · subst h; simp
  · simp [h]


open Classical in
theorem singleF_mul_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (x : v.adicCompletion F)
    (y : w.adicCompletion F) : singleF F v x * singleF F w y = 0 := by
  apply FiniteAdeleRing.ext; intro u
  change Pi.single v x u * Pi.single w y u = 0
  by_cases hu : u = v
  · subst hu; simp [Ne.symm h]
  · simp [hu]

theorem compAt_tmul (v : HeightOneSpectrum (𝓞 F)) (a : FiniteAdeleRing (𝓞 F) F) (b : E) :
    compAt E v (a ⊗ₜ b) = evalAt F v a ⊗ₜ b := rfl

theorem singleV_tmul (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F) (b : E) :
    singleV E v (a ⊗ₜ b) = singleF F v a ⊗ₜ b := rfl

theorem sigA_tmul (c : E ≃ₐ[F] E) (a : FiniteAdeleRing (𝓞 F) F) (b : E) :
    sigA c (a ⊗ₜ b) = a ⊗ₜ c b := rfl

theorem sigV_tmul (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F) (b : E) :
    sigV c v (a ⊗ₜ b) = a ⊗ₜ c b := rfl

theorem compAt_singleV_self (v : HeightOneSpectrum (𝓞 F)) (x : Kv E v) :
    compAt E v (singleV E v x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [singleV_tmul, compAt_tmul, evalAt_singleF_self]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem compAt_singleV_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (x : Kv E v) :
    compAt E w (singleV E v x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [singleV_tmul, compAt_tmul, evalAt_singleF_ne h, zero_tmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]

theorem singleV_mul (v : HeightOneSpectrum (𝓞 F)) (x y : Kv E v) :
    singleV E v (x * y) = singleV E v x * singleV E v y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [add_mul, map_add (f := _), map_add (f := _), hx, hx', add_mul]
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => rw [mul_add, map_add (f := _), map_add (f := _), hy, hy', mul_add]
    | tmul a' b' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, singleV_tmul, singleV_tmul, singleV_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, singleF_mul]

theorem singleV_mul_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (x : Kv E v) (y : Kv E w) :
    singleV E v x * singleV E w y = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [map_add (f := _), add_mul, hx, hx', add_zero]
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => rw [map_add (f := _), mul_add, hy, hy', add_zero]
    | tmul a' b' =>
      rw [singleV_tmul, singleV_tmul, Algebra.TensorProduct.tmul_mul_tmul, singleF_mul_ne h,
        zero_tmul]

theorem singleV_mul_inclV (v : HeightOneSpectrum (𝓞 F)) (x : Kv E v) (y : E) :
    singleV E v (x * inclV E v y) = singleV E v x * inclA F E y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [add_mul, map_add (f := _), map_add (f := _), hx, hx', add_mul]
  | tmul a b =>
    show singleV E v (a ⊗ₜ b * 1 ⊗ₜ y) = singleV E v (a ⊗ₜ b) * (1 ⊗ₜ y)
    rw [Algebra.TensorProduct.tmul_mul_tmul, singleV_tmul, singleV_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]

theorem sigA_singleV (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : Kv E v) :
    sigA c (singleV E v x) = singleV E v (sigV c v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [map_add (f := _), map_add (f := _), hx, hx', map_add (f := _), map_add (f := _)]
  | tmul a b => rw [singleV_tmul, sigA_tmul, sigV_tmul, singleV_tmul]

theorem compAt_sigA (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : AE F E) :
    compAt E v (sigA c a) = sigV c v (compAt E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [map_add (f := _), map_add (f := _), hx, hx', map_add (f := _), map_add (f := _)]
  | tmul a b => rw [sigA_tmul, compAt_tmul, compAt_tmul, sigV_tmul]

theorem compAt_inclA (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    compAt E v (inclA F E x) = inclV E v x := by
  show compAt E v (1 ⊗ₜ x) = 1 ⊗ₜ x
  rw [compAt_tmul, map_one]

theorem compAt_separates (a b : AE F E) (h : ∀ v, compAt E v a = compAt E v b) : a = b := by
  let 𝒞 := Module.Free.chooseBasis F E
  have key : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : AE F E) k,
      equivFinsuppOfBasisRight 𝒞 (compAt E v x) k =
        evalAt F v (equivFinsuppOfBasisRight 𝒞 x k) := by
    intro v x k
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [compAt_tmul, equivFinsuppOfBasisRight_apply_tmul_apply,
        equivFinsuppOfBasisRight_apply_tmul_apply, map_smul]
    | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  apply (equivFinsuppOfBasisRight 𝒞).injective
  refine Finsupp.ext fun k => FiniteAdeleRing.ext _ fun w => ?_
  have hk := congrArg (fun z => equivFinsuppOfBasisRight 𝒞 z k) (h w)
  simp only [key] at hk
  exact hk

theorem matrix_separates {N : ℕ} (X Y : Matrix (Fin N) (Fin N) (AE F E))
    (h : ∀ v, X.map (compAt E v) = Y.map (compAt E v)) : X = Y := by
  ext i j
  exact compAt_separates _ _ fun v => congrFun (congrFun (h v) i) j

theorem embed_map_self (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (g : Matrix (Fin N) (Fin N) (Kv E v)) :
    (embed E v g).map (compAt E v) = g := by
  ext i j
  by_cases hij : i = j <;> simp [embed, hij, compAt_singleV_self]

theorem embed_map_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) {N : ℕ}
    (g : Matrix (Fin N) (Fin N) (Kv E v)) : (embed E v g).map (compAt E w) = 1 := by
  ext i j
  by_cases hij : i = j <;> simp [embed, Matrix.one_apply, hij, compAt_singleV_ne h]

theorem inclA_map_compAt (v : HeightOneSpectrum (𝓞 F)) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) :
    (J.map (inclA F E)).map (compAt E v) = J.map (inclV E v) := by
  ext i j
  simp [compAt_inclA]

theorem sigA_map_compAt (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {N : ℕ}
    (X : Matrix (Fin N) (Fin N) (AE F E)) :
    (X.map (sigA c)).map (compAt E v) = (X.map (compAt E v)).map (sigV c v).toRingHom := by
  ext i j
  simp [compAt_sigA]

theorem form_map_compAt (c : E ≃ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (X : Matrix (Fin N) (Fin N) (AE F E)) :
    (Xᵀ * J.map (inclA F E) * X.map (sigA c)).map (compAt E w) =
      (X.map (compAt E w))ᵀ * J.map (inclV E w) * (X.map (compAt E w)).map (sigV c w).toRingHom := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, inclA_map_compAt, sigA_map_compAt]

end Lemmas

theorem intersectionNumber_baseChange : PlaceMaps.Statement := by
  intro F E _ _ _ _ _ c _ _
  refine ⟨compAt_separates, fun v => ⟨compAt_singleV_self v, fun w h => compAt_singleV_ne h,
    singleV_mul v, fun w h => singleV_mul_ne h, singleV_mul_inclV v, sigA_singleV c v,
    compAt_sigA c v, compAt_inclA v, fun N => ⟨?_, ?_, fun J => ⟨?_, ?_⟩⟩⟩⟩
  · apply matrix_separates; intro w
    by_cases hw : w = v
    · subst hw; rw [embed_map_self]; simp
    · rw [embed_map_ne hw]; simp
  · intro g h
    apply matrix_separates; intro w
    rw [Matrix.map_mul]
    by_cases hw : w = v
    · subst hw; rw [embed_map_self, embed_map_self, embed_map_self]
    · rw [embed_map_ne hw, embed_map_ne hw, embed_map_ne hw, mul_one]
  · rintro g ⟨hdet, hJ⟩
    refine ⟨?_, ?_⟩
    · apply compAt_separates; intro w
      rw [RingHom.map_det, RingHom.mapMatrix_apply, map_one]
      by_cases hw : w = v
      · subst hw; rw [embed_map_self, hdet]
      · rw [embed_map_ne hw, det_one]
    · apply matrix_separates; intro w
      rw [form_map_compAt, inclA_map_compAt]
      by_cases hw : w = v
      · subst hw; rw [embed_map_self]; exact hJ
      · rw [embed_map_ne hw]; simp
  · rintro x ⟨hdet, hJ⟩
    refine ⟨?_, ?_⟩
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]
    · have : (xᵀ * J.map (inclA F E) * x.map (sigA c)).map (compAt E v) =
          (J.map (inclA F E)).map (compAt E v) := by rw [hJ]
      rw [form_map_compAt, inclA_map_compAt] at this
      exact this

theorem proof (_h : LocalRingHypotheses.Statement) : PlaceMaps.Statement := intersectionNumber_baseChange

end PlaceMaps

end StrongApprox

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PSAHolds
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem SAHolds.of_neighbourhoods_truncation (hNb : AENeighbourhoods.Statement)
    (hTr : Truncation.Statement) : SAHolds.Statement := by
  classical
  intro F E _ _ _ _ _ c hrk hc N J hJ hdet hiso _ _ x hx
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 F) F) (AE F E)
  obtain ⟨hN1, hN2⟩ := hNb F E c hrk hc
  change x ∈ Cl c J
  rw [Cl, ← closure_closure, mem_closure_iff_nhds]
  intro U hU
  have hU' : (fun M => x + M) ⁻¹' U ∈ 𝓝 (0 : Matrix (Fin N) (Fin N) (AE F E)) := by
    have hcont : Continuous (fun M : Matrix (Fin N) (Fin N) (AE F E) => x + M) :=
      continuous_const.add continuous_id
    apply hcont.continuousAt.preimage_mem_nhds
    simpa using hU
  obtain ⟨S₀, hS₀⟩ := hN1 N _ hU'
  choose T hT using fun p : Fin N × Fin N => hN2 (x p.1 p.2)
  set S : Finset (HeightOneSpectrum (𝓞 F)) := S₀ ∪ Finset.univ.biUnion T with hSdef
  obtain ⟨t1, t2, -, t4⟩ := hTr F E c hrk hc N J hJ hdet hiso S x
  refine ⟨trunc E S x, ?_, t4 hx⟩
  have hmem : x + (trunc E S x - x) ∈ U := by
    apply hS₀
    intro i j
    have hS : ∀ v ∈ S, compAt E v ((trunc E S x - x) i j) = 0 := by
      intro v hv
      have h := congrFun (congrFun (t1 v hv) i) j
      simp only [Matrix.map_apply] at h
      rw [Matrix.sub_apply, map_sub, h, sub_self]
    refine ⟨fun v hv => hS v (Finset.mem_union_left _ hv), fun v hv => ?_⟩
    by_cases hvS : v ∈ S
    · rw [hS v hvS]; exact zero_mem _
    · have h := congrFun (congrFun (t2 v hvS) i) j
      simp only [Matrix.map_apply] at h
      have hvT : v ∉ T (i, j) := fun h' =>
        hvS (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨(i, j), Finset.mem_univ _, h'⟩))
      have hx' : compAt E v (x i j) ∈ intAt E v := hT (i, j) v hvT
      rw [Matrix.sub_apply, map_sub, h]
      refine sub_mem ?_ hx'
      rw [Matrix.one_apply]
      split_ifs
      · exact AddSubgroup.subset_closure
          ⟨1, one_mem _, 1, by simp [Algebra.TensorProduct.one_def]⟩
      · exact zero_mem _
  simpa using hmem

theorem SAHolds.proof (_hHyp : HypPairExists.Statement) (hNb : AENeighbourhoods.Statement)
    (hTr : Truncation.Statement) : SAHolds.Statement :=
  SAHolds.of_neighbourhoods_truncation hNb hTr

end StrongApprox

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StrongApproximation.PSAOpenHolds
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

theorem map_inclA_mem_SU {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (c : E ≃ₐ[F] E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) {γ : Matrix (Fin N) (Fin N) E}
    (hγ : γ ∈ SU c.toRingHom J) :
    γ.map (inclA F E) ∈ SU (sigA c) (J.map (inclA F E)) := by
  obtain ⟨hdet, hform⟩ := hγ
  have hsig : ∀ y : E, sigA c (inclA F E y) = inclA F E (c y) := by
    intro y
    simp [sigA, inclA, Algebra.TensorProduct.map_tmul]
  have hmap : (γ.map (inclA F E)).map (sigA c) = (γ.map c.toRingHom).map (inclA F E) := by
    ext i j
    simp [hsig]
  refine ⟨?_, ?_⟩
  · rw [show (γ.map (inclA F E)).det = inclA F E γ.det from (RingHom.map_det _ _).symm, hdet, map_one]
  · rw [hmap, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hform]

theorem SAOpenHolds.proof (hSA : SAHolds.Statement) (hTop : AETopologicalRing.Statement) :
    SAOpenHolds.Statement := by
  intro F E _ _ _ _ _ c h2 hc N J hJ hdet hiso _ _ Kg hKsub h1 _ hinv hO x hx
  obtain ⟨O, hOopen, hOK⟩ := hO
  have hxdet : IsUnit x.det := by rw [hx.1]; exact isUnit_one

  have hcont : Continuous (fun g : Matrix (Fin N) (Fin N) (AE F E) => x⁻¹ * g) :=
    ((hTop F E c h2 hc).2.2.2 N (J.map (inclA F E))).1.comp
      (continuous_const.prodMk continuous_id)
  have hUopen : IsOpen ((fun g : Matrix (Fin N) (Fin N) (AE F E) => x⁻¹ * g) ⁻¹' O) :=
    hOopen.preimage hcont
  have h1O : (1 : Matrix (Fin N) (Fin N) (AE F E)) ∈ O := by
    rw [← hOK] at h1; exact h1.1
  have hxU : x ∈ (fun g : Matrix (Fin N) (Fin N) (AE F E) => x⁻¹ * g) ⁻¹' O := by
    change x⁻¹ * x ∈ O
    rw [nonsing_inv_mul x hxdet]; exact h1O
  have hcl := hSA F E c h2 hc N J hJ hdet hiso hx
  obtain ⟨_, hyU, ⟨γ, hγ, rfl⟩⟩ := mem_closure_iff.1 hcl _ hUopen hxU
  have hγA := map_inclA_mem_SU c J hγ
  set k := x⁻¹ * γ.map (inclA F E) with hk
  have hkSU : k ∈ SU (sigA c) (J.map (inclA F E)) :=
    mul_mem_SU (inv_mem_SU _ _ hx) hγA
  have hkK : k ∈ Kg := by rw [← hOK]; exact ⟨hyU, hkSU⟩
  have hkdet : IsUnit k.det := by rw [hkSU.1]; exact isUnit_one
  refine ⟨γ, hγ, k⁻¹, hinv k hkK, ?_⟩
  have hxk : x * k = γ.map (inclA F E) := by
    rw [hk, ← Matrix.mul_assoc, mul_nonsing_inv x hxdet, Matrix.one_mul]
  rw [← hxk, Matrix.mul_assoc, mul_nonsing_inv k hkdet, Matrix.mul_one]

end GroundTheory.Heights₂.Heights.StrongApprox
end
end

