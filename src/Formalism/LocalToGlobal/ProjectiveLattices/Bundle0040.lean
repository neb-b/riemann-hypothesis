module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
public import Formalism.LocalToGlobal.ProjectiveLattices.LocalUnitReduction.IsUnitMkOfForallPrime
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)


set_option maxHeartbeats 1000000 in
abbrev phiI (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (Z : Comp (T.Q.Xo j) T.Q.c) :=
  phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w

def CurveHyp (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore))
    (g0 : (recB h.toLawsCore).Cusp j wF) : Prop :=
  SpanW (recPlus h j hj) G.w S ∧ BigAt h j hj hG G ∧ ThAt h j hj hG G g0 ∧ (recPlus h j hj).NonZeroComp wF g0


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem curveInst_of [Fintype (Comp (T.Q.Xo j) T.Q.c)]
    (hinj : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ f : ↥(Frac0 (recPlus h j hj) la G.w), (∀ Z, phiI h j hj hG hT la G Z f = 0) → f = 0)
    (hone : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
        ∀ Z Z', RingHom.ker (phiI h j hj hG hT la G Z) ≤ Q → RingHom.ker (phiI h j hj hG hT la G Z') ≤ Q → Z = Z')
    (hloc : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ Z (r : RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w),
        ∃ a p : ↥(Frac0 (recPlus h j hj) la G.w),
          (∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
            RingHom.ker (phiI h j hj hG hT la G Z) ≤ Q → p ∉ Q) ∧
          phiI h j hj hG hT la G Z p * r = phiI h j hj hG hT la G Z a)
    (hS1 : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 → ∀ Z,
      FiniteDimensional (Kp (recPlus h j hj) la G.N)
          (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
            Ideal.map (phiI h j hj hG hT la G Z) (Jid (recPlus h j hj) la G.w)) ∧
        IsReduced (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
          Ideal.map (phiI h j hj hG hT la G Z) (Jid (recPlus h j hj) la G.w)))
    (hH2 : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ (e : ℕ) (w' : WeightFamilies.Wt D j) (θ : (recB h.toLawsCore).Cusp j w') (hw : wadd wF w' = wsmul e wL),
        (∀ Z, evC hG Z ((θ : (recB h.toLawsCore).Cusp j w') : T.R j) ≠ 0) →
        IsUnit (toOsK (recPlus h j hj) la G.w (u0 (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la g0 θ hw)))
    (hH3 : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ b : ↥(Frac0 (recPlus h j hj) la G.w),
        (b : Lw (recPlus h j hj) la G.w) *
          algebraMap (Rp (recPlus h j hj) la G.N) (Lw (recPlus h j hj) la G.w)
            (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc wF g0)) = 0 → b = 0) :
    CurveInstSt h j hj := by
  intro _ ka wL wF G la S g0 hSp hBig hTh hNZ
  have hH : CurveHyp h j hj hG ka wL wF G S g0 := ⟨hSp, hBig, hTh, hNZ⟩
  have h1 := LocalUnitReduction.finRed (Kp (recPlus h j hj) la G.N) ↥(Frac0 (recPlus h j hj) la G.w) (Jid (recPlus h j hj) la G.w)
    (Comp (T.Q.Xo j) T.Q.c) (fun Z => RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w)
    (fun Z => phiI h j hj hG hT la G Z) (hinj _ _ _ G S g0 la hH) (hone _ _ _ G S g0 la hH)
    (hloc _ _ _ G S g0 la hH) (hS1 _ _ _ G S g0 la hH)
  obtain ⟨e, w', θ, hw, hθ⟩ := hTh
  exact curveModel_of_fr (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la g0 h1.1 h1.2 θ hw
    (hH2 _ _ _ G S g0 la hH e w' θ hw hθ) (hH3 _ _ _ G S g0 la hH)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CurveCountB
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor MvPolynomial

namespace CurveCount

variable {K : Type*} [Field K] {N : ℕ}

def homog (a : Fin N) (Q : MvPolynomial (Fin N) K) : MvPolynomial (Fin N) K :=
  ∑ m ∈ Q.support, monomial (m + Finsupp.single a (Q.totalDegree - m.degree)) (Q.coeff m)

theorem homog_isHomogeneous (a : Fin N) (Q : MvPolynomial (Fin N) K) :
    (homog a Q).IsHomogeneous Q.totalDegree := by
  classical
  refine IsHomogeneous.sum _ _ _ fun m hm => isHomogeneous_monomial _ ?_
  have hle : m.degree ≤ Q.totalDegree := le_totalDegree hm
  rw [map_add (f := _), Finsupp.degree_single]
  omega

theorem aeval_homog {L : Type*} [Field L] [Algebra K L] (a : Fin N) (Q : MvPolynomial (Fin N) K) (y : Fin N → L)
    (hy : y a ≠ 0) : aeval y (homog a Q) = y a ^ Q.totalDegree * aeval (fun i => y i / y a) Q := by
  classical
  have hQ : aeval (fun i => y i / y a) Q =
      ∑ m ∈ Q.support, aeval (fun i => y i / y a) (monomial m (Q.coeff m)) := by
    conv_lhs => rw [Q.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hQ, homog, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hle : m.degree ≤ Q.totalDegree := le_totalDegree hm
  rw [aeval_monomial, aeval_monomial, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
    Finsupp.prod_single_index (by simp)]
  simp only [Finsupp.prod, div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  have hd : m.degree = ∑ i ∈ m.support, m i := rfl
  rw [← hd]
  have e : y a ^ Q.totalDegree = y a ^ (Q.totalDegree - m.degree) * y a ^ m.degree := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [e]
  field_simp

theorem adjoin_ratio_eq {L : Type*} [Field L] [Algebra K L] (v : Fin N → L) {a b : Fin N} (ha : v a ≠ 0)
    (hb : v b ≠ 0) :
    IntermediateField.adjoin K (Set.range fun i => v i / v a) = IntermediateField.adjoin K (Set.range fun i => v i / v b) := by
  have key : ∀ a b : Fin N, v a ≠ 0 → v b ≠ 0 →
      IntermediateField.adjoin K (Set.range fun i => v i / v a) ≤ IntermediateField.adjoin K (Set.range fun i => v i / v b) := by
    intro a b ha hb
    rw [IntermediateField.adjoin_le_iff, Set.range_subset_iff]
    intro i
    have e : v i / v a = (v i / v b) / (v a / v b) := by field_simp
    rw [SetLike.mem_coe, e]
    exact IntermediateField.div_mem _ (IntermediateField.subset_adjoin K _ ⟨i, rfl⟩)
      (IntermediateField.subset_adjoin K _ ⟨a, rfl⟩)
  exact le_antisymm (key a b ha hb) (key b a hb ha)

end CurveCount

namespace CurveLoc

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

theorem tv_indep :
    AlgebraicIndependent (X.Kl la) (fun p : Idx D j N => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p)) := by
  have h0 := MvPolynomial.algebraicIndependent_X (Idx D j N) (X.Ol la)
  have hinj1 : Function.Injective (algebraMap (Pol X la N) (Op X la N)) :=
    IsLocalization.injective (Op X la N) (Ideal.primeCompl_le_nonZeroDivisors (gI X la N))
  have hinj2 : Function.Injective (@algebraMap (Op X la N) (Kp X la N) _ _ _) := IsFractionRing.injective _ _
  let g : Pol X la N →ₐ[X.Ol la] Kp X la N :=
    (IsScalarTower.toAlgHom (X.Ol la) (Op X la N) (Kp X la N)).comp
      (IsScalarTower.toAlgHom (X.Ol la) (Pol X la N) (Op X la N))
  have h1 : AlgebraicIndependent (X.Ol la)
      (fun p : Idx D j N => @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p)) :=
    h0.map' (f := g) (hinj2.comp hinj1)
  have : Algebra.IsAlgebraic (X.Ol la) (X.Kl la) := IsLocalization.isAlgebraic (X.Kl la) (nonZeroDivisors (X.Ol la))
  exact h1.extendScalars (X.Kl la)

theorem sfr_eq (i : Fin (WeightFamilies.dimY D j + 1)) :
    sfr X la w i = ∑ k, algebraMap (Kp X la N) ↥(Frac0 X la w)
      (@algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N (i, k))) * xw X la N w k := by
  apply Subtype.ext
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coe_sfr, Formalism.MainNotions.Gaps.EtaleWeightGaps.sec, map_sum]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Algebra.smul_def]
  rfl

theorem sfr_zero : sfr X la w 0 = 1 := by
  apply Subtype.ext
  rw [coe_sfr, frac_apply, pow_one, section_mul_inverse_eq_one]
  rfl

variable {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem countQAt_of (v : Fin N → Ω) (hv : ∀ i, gF (X.inc wL (w i)) = v i)
    (htr : ∃ a₀, v a₀ ≠ 0 ∧
      Algebra.trdeg B.KO (IntermediateField.adjoin B.KO (Set.range fun i => v i / v a₀)) ≤ WeightFamilies.dimY D j) :
    CountQAt X la N w gF := by
  classical
  intro 𝔮 h𝔮 hJ hK Pw k hPw hne hmem
  have : 𝔮.IsPrime := h𝔮
  have hvf : (fun i => gF (X.inc wL (w i))) = v := funext hv
  rw [hvf] at hne
  let Fr := ↥(Frac0 X la w)
  let κ := FractionRing (Fr ⧸ 𝔮)
  let ρ : Fr →+* κ := (algebraMap (Fr ⧸ 𝔮) κ).comp (Ideal.Quotient.mk 𝔮)
  have hρ : ∀ f, ρ f = 0 ↔ f ∈ 𝔮 := fun f => by
    rw [RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  let ρK : Kp X la N →+* κ := ρ.comp (algebraMap (Kp X la N) Fr)
  let algKl : Algebra (X.Kl la) κ := (ρK.comp (algebraMap (X.Kl la) (Kp X la N))).toAlgebra
  let algK : Algebra B.KO κ :=
    ((ρK.comp (algebraMap (X.Kl la) (Kp X la N))).comp (algebraMap B.KO (X.Kl la))).toAlgebra
  let _ := algKl
  let _ := algK
  have : IsScalarTower B.KO (X.Kl la) κ :=
    @IsScalarTower.of_algebraMap_eq B.KO (X.Kl la) κ _ _ _ _ algKl algK (fun _ => rfl)
  let x : Fin N → κ := fun i => ρ (xw X la N w i)
  let t : Fin (WeightFamilies.dimY D j + 1) × Fin N → κ :=
    fun p => ρK (@algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N p))
  have ht : AlgebraicIndependent B.KO t := by
    let g : Kp X la N →ₐ[X.Kl la] κ := { ρK with commutes' := fun _ => rfl }
    have h1 := (tv_indep X la N).map' (f := g) ρK.injective
    exact h1.restrictScalars (algebraMap B.KO (X.Kl la)).injective
  have hρpol : ∀ Q : MvPolynomial (Fin N) B.KO, ρ (polX X la N w Q) = aeval x Q := fun Q => by
    rw [polX, MvPolynomial.eval₂_comp_left, aeval_def]
    rfl
  have hlin : ∀ i : Fin (WeightFamilies.dimY D j), ∑ k, t (i.succ, k) * x k = 0 := by
    intro i
    have h := congrArg ρ (sfr_eq X la N w i.succ)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h
    simp only [map_mul] at h
    rw [← (hρ _).mpr (hJ (sfr_succ_mem_Jid X la w i)), h]
    rfl
  have hlin0 : ∑ k, t (0, k) * x k = 1 := by
    have h := congrArg ρ (sfr_eq X la N w 0)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, sfr_zero, map_one] at h
    simp only [map_mul] at h
    rw [h]
    rfl
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hlin0.symm ▸ one_ne_zero : ∑ k, t (0, k) * x k ≠ 0)
  have hxa : x a ≠ 0 := right_ne_zero_of_mul ha
  have hva : v a ≠ 0 := by
    intro h0
    apply hxa
    refine (hρ _).mpr (hK ?_)
    rw [RingHom.mem_ker, phiZ_xw, hv, h0, map_zero, zero_mul]
  obtain ⟨a₀, ha₀, htr₀⟩ := htr
  have htra : Algebra.trdeg B.KO (IntermediateField.adjoin B.KO (Set.range fun i => v i / v a)) ≤ WeightFamilies.dimY D j := by
    rw [CurveCount.adjoin_ratio_eq v hva ha₀]
    exact htr₀
  have htrans : ∀ Q : MvPolynomial (Fin N) B.KO, aeval (fun i => v i / v a) Q = 0 →
      aeval (fun i => x i / x a) Q = 0 := by
    intro Q hQ
    have hH := CurveCount.homog_isHomogeneous a Q
    have hv0 : aeval v (CurveCount.homog a Q) = 0 := by rw [CurveCount.aeval_homog a Q v hva, hQ, mul_zero]
    have hq : polX X la N w (CurveCount.homog a Q) ∈ 𝔮 := hK (by
      rw [RingHom.mem_ker, phiZ_polX X la N w gF hH, hvf, hv0, map_zero, mul_zero])
    have hx0 : aeval x (CurveCount.homog a Q) = 0 := by rw [← hρpol]; exact (hρ _).mpr hq
    rw [CurveCount.aeval_homog a Q x hxa] at hx0
    exact (mul_eq_zero.mp hx0).resolve_left (pow_ne_zero _ hxa)
  exact CurveCount.countCore v x a hva hxa htra htrans t ht hlin hlin0 Pw hPw hne
    (by rw [← hρpol]; exact (hρ _).mpr hmem)

end CurveLoc

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CurveInj
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct

namespace CurveInj

section Lin

variable {k V M : Type*} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup M] [Module k M]

def evDual (φ : Module.Dual k V) : V ⊗[k] M →ₗ[k] M :=
  TensorProduct.lid k M ∘ₗ TensorProduct.map φ LinearMap.id

theorem evDual_tmul (φ : Module.Dual k V) (v : V) (m : M) : evDual φ (v ⊗ₜ[k] m) = φ v • m := by
  simp [evDual]

end Lin

theorem coeff_eq_zero {K Kl K' C : Type*} [Field K] [Field Kl] [Field K'] [Algebra K Kl] [Algebra Kl K']
    [AddCommGroup C] [Module K C] {κ : Type*} [Fintype κ] (b : Module.Basis κ K C)
    {ι : Type*} (Ω : ι → Type*) [∀ Z, AddCommGroup (Ω Z)] [∀ Z, Module K (Ω Z)]
    (ev : ∀ Z, C →ₗ[K] Ω Z) (hev : ∀ F : C, (∀ Z, ev Z F = 0) → F = 0)
    (c : κ → K') (hc : ∀ Z, ∑ i, c i ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] ev Z (b i)) = 0) : c = 0 := by
  funext i₀
  refine (Module.forall_dual_apply_eq_zero_iff Kl (c i₀)).1 fun φ => ?_
  refine (Module.forall_dual_apply_eq_zero_iff K (φ (c i₀))).1 fun ψ => ?_
  have hF : (∑ i, ψ (φ (c i)) • b i) = 0 := by
    refine hev _ fun Z => ?_
    have h := congrArg (fun t => evDual (M := Ω Z) ψ (evDual (M := Kl ⊗[K] Ω Z) φ t)) (hc Z)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, evDual_tmul, map_zero, TensorProduct.smul_tmul', smul_eq_mul, mul_one] at h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simpa only [map_smul] using h
  exact Fintype.linearIndependent_iff.1 b.linearIndependent _ hF i₀

section Gen

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) {ι : Type} (Ω : ι → Type) [∀ Z, CommRing (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)]
  (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)

theorem vw_inj (u : WeightFamilies.Wt D j) (hinj : ∀ F : B.Cusp j u, (∀ Z, gF Z (X.inc u F) = 0) → F = 0)
    {g : Rp X la N} (hg : g ∈ Vw X la N u) (h0 : ∀ Z, rzMap X la N (Ω Z) (gF Z) g = 0) : g = 0 := by
  classical
  let b := Module.finBasis B.KO (B.Cusp j u)
  have hs : Submodule.span B.KO (Set.range b) = ⊤ := b.span_eq
  rw [Vw_eq_span_image X la N u hs, ← Set.range_comp] at hg
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (Kp X la N)).1 hg
  have hc : c = 0 := by
    refine coeff_eq_zero (K := B.KO) (Kl := X.Kl la) (K' := Kp X la N) b Ω
      (fun Z => (gF Z).toLinearMap ∘ₗ X.inc u) (fun F hF => hinj F hF) c fun Z => ?_
    refine (Finset.sum_congr rfl fun i _ => ?_).trans ((map_sum _ _ _).symm.trans (h0 Z))
    rw [map_smul, Function.comp_apply, rzMap_emb, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  simp [hc]

theorem fraction_zero_injective [Finite ι] {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)
    (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ Z, gF Z (X.inc u F) = 0) → F = 0)
    (f : ↥(Frac0 X la w)) (hf : ∀ Z, phiZ X la N (Ω Z) (gF Z) w f = 0) : f = 0 := by
  classical
  cases nonempty_fintype ι
  obtain ⟨k, g, hg, hfg⟩ := (mem_Hfr X la w).1 ((mem_Frac0 X la w).1 f.2)
  have hZ : ∀ Z, ∃ n : ℕ, rzMap X la N (Ω Z) (gF Z) (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0 ^ n * g) = 0 := by
    intro Z
    have h1 := hf Z
    rw [phiZ_apply, hfg, frac_apply, map_mul, map_pow] at h1
    have hu : IsUnit (lwZ X la N (Ω Z) (gF Z) w (w0inv X la w)) := by
      refine IsUnit.of_mul_eq_one (lwZ X la N (Ω Z) (gF Z) w (algebraMap (Rp X la N) (Lw X la w) (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))) ?_
      rw [← map_mul, mul_comm, section_mul_inverse_eq_one, map_one]
    rw [(hu.pow k).mul_left_eq_zero, lwZ_alg,
      IsLocalization.map_eq_zero_iff (Submonoid.powers (rzMap X la N (Ω Z) (gF Z) (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)))] at h1
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := h1
    exact ⟨n, by rw [map_mul, map_pow]; exact hn⟩
  choose n hn using hZ
  have hM : ∀ Z, rzMap X la N (Ω Z) (gF Z) (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0 ^ (Finset.univ.sup n) * g) = 0 := by
    intro Z
    have hle : n Z ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ Z)
    rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, map_mul, hn Z, mul_zero]
  have h0 := vw_inj X la N Ω gF _ (hinj _) (sec_pow_mul_mem X la w 0 (wt0 D j) k (Finset.univ.sup n) hg) hM
  apply Subtype.ext
  show (f : Lw X la w) = 0
  rw [hfg, frac_eq_zero_iff]
  exact ⟨_, h0⟩

end Gen

end CurveInj

section Inst

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)

theorem curveInj [Finite (Comp (T.Q.Xo j) T.Q.c)] (hV : GenValInjSt h j hG) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO))
    (f : ↥(Frac0 (recPlus h j hj) la G.w))
    (hf : ∀ Z : Comp (T.Q.Xo j) T.Q.c,
      phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w f = 0) : f = 0 :=
  CurveInj.fraction_zero_injective (recPlus h j hj) la G.N (fun Z : Comp (T.Q.Xo j) T.Q.c => Om Z)
    (fun Z => formsEvR j hG hT Z) G.w
    (fun u F hF => hV u F fun Z => (formsEvR_single j hG hT Z _ _).symm.trans (hF Z)) f hf

end Inst

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ESecPfA
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {T : Top D} (h : LawsP T) {j : ℕ} (hj : InR D j)

include h hj

theorem esec_mem_C {w : WeightFamilies.Wt D j} {f : T.R j} : f ∈ cutR T.C j w ↔ f ∈ T.C j w := by
  rw [cutR_eq T.C hj]

theorem esec_mul_mem {w w' : WeightFamilies.Wt D j} {f g : T.R j} (hf : f ∈ cutR T.C j w) (hg : g ∈ cutR T.C j w') :
    f * g ∈ cutR T.C j (wadd w w') := by
  rw [esec_mem_C h hj] at hf hg ⊢
  exact h.toLawsCore.mul j hj w w' f hf g hg

def esecMul {w w' : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j w) (F' : (recB h.toLawsCore).Cusp j w') :
    (recB h.toLawsCore).Cusp j (wadd w w') :=
  ⟨(F : T.R j) * (F' : T.R j), esec_mul_mem h hj F.2 F'.2⟩

theorem esecMul_coe {w w' : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j w)
    (F' : (recB h.toLawsCore).Cusp j w') :
    ((esecMul h hj F F' : (recB h.toLawsCore).Cusp j (wadd w w')) : T.R j) = (F : T.R j) * (F' : T.R j) := rfl

theorem esec_inc_mul {w w' : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j w)
    (F' : (recB h.toLawsCore).Cusp j w') :
    (recPJ h j hj).inc (wadd w w') (esecMul h hj F F') = (recPJ h j hj).inc w F * (recPJ h j hj).inc w' F' :=
  (incG_mul deg (cutR T.C j) (deg_wadd w w') F F' (esec_mul_mem h hj F.2 F'.2)).symm

def esecW (wL : WeightFamilies.Wt D j) : ℕ → WeightFamilies.Wt D j
  | 0 => wL
  | n + 1 => wadd wL (esecW wL n)

omit h hj in
theorem esecW_eq (wL : WeightFamilies.Wt D j) (n : ℕ) : esecW wL n = addL (wt0 D j) wL (n + 1) := by
  induction n with
  | zero => exact (add_zero_weight_one_eq wL).symm
  | succ n ih => rw [esecW, ih, wadd_addL]

def esecPow {wL : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j wL) :
    (n : ℕ) → (recB h.toLawsCore).Cusp j (esecW wL n)
  | 0 => F
  | n + 1 => esecMul h hj F (esecPow F n)

theorem esec_inc_pow {wL : WeightFamilies.Wt D j} (F : (recB h.toLawsCore).Cusp j wL) (n : ℕ) :
    (recPJ h j hj).inc (esecW wL n) (esecPow h hj F n) = (recPJ h j hj).inc wL F ^ (n + 1) := by
  induction n with
  | zero => rw [zero_add, pow_one]; rfl
  | succ n ih =>
    show (recPJ h j hj).inc (wadd wL (esecW wL n)) (esecMul h hj F (esecPow h hj F n)) = _
    rw [esec_inc_mul, ih, pow_succ' _ (n + 1)]

theorem esec_mem_mulL {wL : WeightFamilies.Wt D j} {a b : ℕ} {f g : T.R j}
    (hf : f ∈ cutR T.C j (addL (wt0 D j) wL a)) (hg : g ∈ cutR T.C j (addL (wt0 D j) wL b)) :
    f * g ∈ cutR T.C j (addL (wt0 D j) wL (a + b)) := by
  have := esec_mul_mem h hj hf hg
  rwa [wadd_addL_addL, zero_weight_add] at this

theorem esec_pow_mem {wL : WeightFamilies.Wt D j} {f : T.R j} (hf : f ∈ cutR T.C j wL) (n : ℕ) :
    f ^ (n + 1) ∈ cutR T.C j (addL (wt0 D j) wL (n + 1)) := by
  induction n with
  | zero => rw [zero_add, pow_one, add_zero_weight_one_eq]; exact hf
  | succ n ih =>
    rw [pow_succ]
    have hf' : f ∈ cutR T.C j (addL (wt0 D j) wL 1) := by rw [add_zero_weight_one_eq]; exact hf
    exact esec_mem_mulL h hj ih hf'

theorem esec_monomial_mem {N : ℕ} {wL : WeightFamilies.Wt D j} (x : Fin N → T.R j) (hx : ∀ i, x i ∈ cutR T.C j wL)
    (α : Fin N →₀ ℕ) :
    α = 0 ∨ (α.prod fun i k => x i ^ k) ∈ cutR T.C j (addL (wt0 D j) wL (α.sum fun _ k => k)) := by
  classical
  induction α using Finsupp.induction with
  | zero => exact Or.inl rfl
  | single_add a b f ha hb ih =>
    right
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.prod_single_index (h := fun i k => x i ^ k) (pow_zero _),
      Finsupp.sum_single_index rfl]
    rcases ih with h0 | hmem
    · subst h0
      simp only [Finsupp.prod_zero_index, Finsupp.sum_zero_index, mul_one, add_zero]
      exact esec_pow_mem h hj (hx a) b
    · exact esec_mem_mulL h hj (esec_pow_mem h hj (hx a) b) hmem

theorem esec_hom_mem {N : ℕ} {wL : WeightFamilies.Wt D j} (x : Fin N → T.R j) (hx : ∀ i, x i ∈ cutR T.C j wL)
    (P : MvPolynomial (Fin N) T.Q.c.F) {k : ℕ} (hP : P.IsHomogeneous (k + 1)) :
    MvPolynomial.aeval x P ∈ cutR T.C j (addL (wt0 D j) wL (k + 1)) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [P.as_sum, map_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  rw [MvPolynomial.aeval_monomial, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have hdeg : (α.sum fun _ k => k) = k + 1 := by
    have := hP (MvPolynomial.mem_support_iff.mp hα)
    rw [Finsupp.weight_apply] at this
    simpa using this
  rcases esec_monomial_mem h hj x hx α with h0 | hmem
  · subst h0
    simp at hdeg
  · rwa [hdeg] at hmem

theorem esec_evC_aeval (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    (Z : Comp (T.Q.Xo j) T.Q.c) {N : ℕ} (x : Fin N → T.R j) (P : MvPolynomial (Fin N) T.Q.c.F) :
    evC hG Z (MvPolynomial.aeval x P) = MvPolynomial.aeval (fun i => evC hG Z (x i)) P := by
  rw [← evCAlg_apply hG hT Z]
  exact DFunLike.congr_fun (MvPolynomial.comp_aeval x (evCAlg hG hT Z)) P

end Formalism.L2.Pj
end
end

