module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.WtMatFix
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0762
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0858
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DeRhamLeFiltrationShift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DeRhamInfFiltration
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0045
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0046
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0701
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylCharacterRegularity.ExistsTens
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.ExistsScalar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CrysSlopes
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.Pst GlobalTheory.PstCoeff UpperTheory.V.Loc

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

section Sat

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem val_inv_eq' (n : ℕ) (a : ℂˣ) :
    (((a⁻¹ * qPow w ((1 - (n : ℝ)) / 2) : ℂˣ) : ℂ)) ^ (-1 : ℤ) =
      ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (a : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), zpow_neg_one, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val, inv_inv,
    coe_qPow, ← Complex.cpow_neg, mul_comm]
  congr 2
  push_cast
  ring

private theorem mem_eig {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRec h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B)
    (g : Weil h) (hg : deg g = -1) (b : ℂ) (hb : b ∈ algSat n (normV w) B) : b ∈ (rc (algNorm σ)).eig g := by
  obtain ⟨hu, -⟩ := GlobalTheory.RecLaws.rec_hasSatGL H σ B hB
  obtain ⟨α, hα⟩ := ParLaws.exists_hasSatake_of_unr H hu
  have hBα : B = Finset.univ.val.map α := hB.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα)
  have e : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) :=
    ParLaws.rec_eq_diag H hα
  have e' : rc (algNorm σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w ((1 - (n : ℝ)) / 2)) := by
    rw [rec_algNorm H, e, WD.lpTw_mk]
    refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
    simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]
  simp only [hBα, algSat, Multiset.map_map, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton,
    Multiset.mem_map] at hb
  obtain ⟨i, -, rfl⟩ := hb
  rw [e', WD.eig_mk, WDRep.diag_ρ, charpoly_diagEnd, hg,
    mem_roots (monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _).ne_zero, IsRoot, eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [val_inv_eq']
  simp

end Sat

private theorem norm_root {l : ℕ} [Fact l.Prime] {x y : Om l} (hy : aeval y (minpoly ℚ_[l] x) = 0) : ‖y‖ = ‖x‖ := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have e : minpoly ℚ_[l] x = minpoly ℚ_[l] y :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx) hy (minpoly.monic hx)
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm, e]

private theorem rep_slope {l : ℕ} [Fact l.Prime] (K : FinExt l) (f : ℕ) (hf : 0 < f)
    (hσ : ∀ x : ↥(K0 K), (((PP l).PD K).σ)^[f] x = x) {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (hc : IsCrys ((PP l).PD K) ρ) (β : Om l)
    (x : V ⊗[ℚ_[l]] Bcr l) (hx : x ∈ Dcris ((PP l).PD K) ρ) (h0 : x ≠ 0)
    (hq : aeval ((φVB ((PP l).PD K) (LL := ℚ_[l]) (V := V) : Module.End ℚ_[l] (V ⊗[ℚ_[l]] Bcr l)) ^ f)
      (minpoly ℚ_[l] β) x = 0) :
    (∀ a : ℤ, DdR ((PP l).PD K) ρ ≤ FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) a →
      ‖((l : Om l) ^ f) ^ (-a) * β‖ ≤ 1) ∧
    ∀ b : ℤ, DdR ((PP l).PD K) ρ ⊓ FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) (b + 1) = ⊥ →
      ‖((l : Om l) ^ f) ^ b * β⁻¹‖ ≤ 1 := by
  let e := Module.finBasis ℚ_[l] V
  obtain ⟨M, M', A, hM, hA, hφ, hρ⟩ := UpperTheory.exists_crystalline_period_matrix_bcris_of_isCrys K ρ e hc
  obtain ⟨F, -, hF⟩ := UpperTheory.frobenius_iterate_matrix_form K M A hA hφ f
  obtain ⟨γ, hγ, hr⟩ := UpperTheory.crystalline_period_matrix_relation K f hσ ρ e M M' hM hρ F hF x hx h0 _
    (minpoly.ne_zero (Algebra.IsIntegral.isIntegral β)) hq
  have hn := norm_root hr
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have := UpperTheory.filtration_entries_of_frobenius_matrix K f hf hσ M M' A F hM hA hφ hF a (UpperTheory.de_rham_le_filtration_shift K ρ e M M' hM hρ a ha) γ hγ
    rwa [norm_mul, hn, ← norm_mul] at this
  · have := UpperTheory.filtration_inverse_frobenius_matrix K f hf hσ M M' A F hM hA hφ hF b (UpperTheory.de_rham_inf_filtration K ρ e M M' hM hρ b hb) γ hγ
    rwa [norm_mul, norm_inv, hn, ← norm_inv, ← norm_mul] at this

end UpperTheory.V.Af

open UpperTheory.V.Af in
theorem UpperTheory.V.Af.crysSlopes :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.CrysSlopes := by
  intro _ F Ω _ _ _ _ _ p _ _ ι n m r _ w A h O _ _ _ Bw hj hcr hJ σ B hB rc hrc hwd b hb
  obtain ⟨T⟩ := tiedP p
  have hp : IsPstAt (PP p) Bw (r.comp (Dec (F := F) A).subtype) := by
    obtain ⟨L, r', h1, h2⟩ := hcr
    exact ⟨L, r', h1, GlobalTheory.PstOfCrys.isPst_of_isCrys T _ h2⟩
  obtain ⟨L, r', hm, hpst, hw⟩ := wdAt_of_isPstAt ι Bw h hj hp
  have hc : IsCrys ((PP p).PD Bw.Kw) (Bw.repE L r') := (hm.isCrysAt_iff (PP p)).1 hcr
  obtain ⟨g, hg⟩ := deg_surjective (h := h) (-1)
  have he := mem_eig hrc σ B hB g hg b hb
  rw [← hwd, hw] at he
  obtain ⟨x, hx, h0, hq⟩ := UpperTheory.crystalline_of_place_over (PP p) ι Bw h hj (Bw.repE L r') hpst hc g hg b he _
    (minpoly.aeval ℚ_[p] (ι.symm b))
  obtain ⟨hf, hσ⟩ := UpperTheory.frobenius_residue_degree_fixes (PP p) Bw h hj
  haveI := L.2
  haveI : FiniteDimensional ℚ_[p] (Fin n → ↥L.1) := Module.Finite.trans ↥L.1 _
  obtain ⟨hlo, hhi⟩ := rep_slope Bw.Kw _ hf hσ (resQ (Bw.repE L r'))
    ((GlobalTheory.BSCoeff.isCrys_resQ_iff (PP p) _).2 hc) (ι.symm b) x (by rw [GlobalTheory.BSCoeff.Dcris_resQ]; exact hx) h0 hq
  have hsplit : ∀ (τ : ↥Bw.Kw.1 →ₐ[ℚ_[p]] Om p) (y : ↥Bw.Kw.1), τ y ∈ L.1 := fun τ y => hm.1 (Bw.LL_split τ y)
  have hJ' : ∀ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[p]] ↥L.1, ∃ τ : F →+* Om p, IsInduced Bw τ τ' := fun τ' =>
    ⟨(L.1.val.comp τ').toRingHom.comp ((Bw.j.comp (algebraMap F Ω)).codRestrict Bw.Kw.1 Bw.j_E), fun _ => rfl⟩
  have hmult : ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[p]] ↥L.1) (c : ℤ), (∀ i, -m i ≠ c) →
      multV ((PP p).PD Bw.Kw) (Bw.repE L r') τ' c = 0 := fun τ' c hc' => by
    obtain ⟨τ, hτ⟩ := hJ' τ'
    have h1 := IsJumpsAt.count_eq (PP p) hm hτ (hJ τ L τ' hτ) c
    rw [Multiset.count_eq_zero.2 (by simpa using hc')] at h1
    exact h1.symm
  have hdR : Bw.IsdRE (PP p) L r' := by
    obtain ⟨τ, hτ⟩ := hJ' (Bw.Kw.1.val.codRestrict L.1.toSubalgebra (hsplit _))
    obtain ⟨L₁, r₁, h1, h2, -⟩ := hJ τ L _ hτ
    exact (hm.isdRAt_iff (PP p)).1 ⟨L₁, r₁, h1, h2⟩
  obtain ⟨k1, k2⟩ := UpperTheory.ddR_le_fil_and_inf_fil_eq_bot_of_hodgeTate_mult (PP p) hsplit (Bw.repE L r') (finiteDimensional_DdR _ _ hdR)
  have hq' : ι.symm ((normV w : ℕ) : ℂ) = (p : Om p) ^ resDeg p w := by
    rw [map_natCast, normV_eq_pow (hj.mem_placesOver h), Nat.cast_pow]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · rw [map_mul, map_zpow₀, map_inv₀, hq']
    refine hhi a (eq_bot_iff.2 fun y hy => ?_)
    have := k2 a fun τ c hc' => hmult τ c fun i => by have := ha i; omega
    have hy1 := hy.1
    rw [DdR_resQ] at hy1
    exact this.le ⟨hy1, hy.2⟩
  · rw [map_mul, map_zpow₀, hq', ← neg_neg a]
    refine hlo (-a) fun y hy => ?_
    rw [DdR_resQ] at hy
    exact k1 (-a) (fun τ c hc' => hmult τ c fun i => by have := ha i; omega) hy

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Filter Topology Matrix

namespace UpperTheory.V.Af.GlobalFixedVectors

theorem sub_fixed {Γ X V : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ Γ X) (hσ : σ.IsIrreducible) (τ : Representation ℂ Γ V)
    (h : ⨆ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)}, LinearMap.range f.1 = ⊤)
    (W : Submodule ℂ V) (hW : ∀ g, ∀ v ∈ W, τ g v ∈ W) (h0 : W ≠ ⊥) (K : Subgroup Γ) (hK : HasFixed σ K) :
    ∃ v ∈ W, v ≠ 0 ∧ ∀ u ∈ K, τ u v = v :=
  _root_.UpperTheory.Reformulated.B.SubgroupFixed.sub_fixed σ hσ τ h W hW h0 K hK

variable {F : Type} [Field F] [NumberField F] {n M : ℕ}

theorem mem_Ohat {x : Af F} : x ∈ Ohat F ↔ ∀ w : HeightOneSpectrum (𝓞 F), pLoc F w x ∈ w.adicCompletionIntegers F := by
  simp [Ohat, Subring.mem_iInf]

theorem gl_ext {g h : GL (Fin n) (Af F)}
    (e : ∀ w, GeneralLinearGroup.map (pLoc F w) g = GeneralLinearGroup.map (pLoc F w) h) : g = h := by
  ext i j : 2
  exact FiniteAdeleRing.ext _ fun w => congrArg (fun x : GL (Fin n) (w.adicCompletion F) => x i j) (e w)

theorem pLoc_sLoc (w : HeightOneSpectrum (𝓞 F)) (x : w.adicCompletion F) : pLoc F w (sLoc F w x) = x := by
  classical
  exact Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) w x

theorem pLoc_sLoc_of_ne {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w) (x : w.adicCompletion F) : pLoc F v (sLoc F w x) = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) h x

theorem sLoc_mem (w : HeightOneSpectrum (𝓞 F)) {x : Af F} (hx : x ∈ Ohat F) : sLoc F w (pLoc F w x) ∈ Ohat F :=
  mem_Ohat.2 fun v => by
    by_cases h : v = w
    · subst h; rw [pLoc_sLoc]; exact mem_Ohat.1 hx v
    · rw [pLoc_sLoc_of_ne h]; exact zero_mem _

noncomputable def eLoc (w : HeightOneSpectrum (𝓞 F)) : Ohat F →ₙ+* Ohat F where
  toFun x := ⟨sLoc F w (pLoc F w x), sLoc_mem w x.2⟩
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

theorem eLoc_eq (w : HeightOneSpectrum (𝓞 F)) (x : Ohat F) : eLoc w x = eLoc w 1 * x := by
  refine Subtype.ext (FiniteAdeleRing.ext _ fun v => ?_)
  change pLoc F v (sLoc F w (pLoc F w x)) = pLoc F v (sLoc F w (pLoc F w (1 : Ohat F)) * x)
  rw [map_mul]
  by_cases h : v = w
  · subst h; simp [pLoc_sLoc]
  · simp [pLoc_sLoc_of_ne h]

theorem loc_mem (w : HeightOneSpectrum (𝓞 F)) {k : GL (Fin n) (Af F)} (hk : k ∈ KLev F n M) :
    GeneralLinearGroup.map (pLoc F w) k ∈ KLoc F w n M := by
  obtain ⟨g, hg, rfl⟩ := hk
  refine ⟨cornerGL n (eLoc w) g, ?_, ?_⟩
  · ext i j
    have h1 := congrArg (fun x : GL (Fin n) (Ohat F ⧸ Ideal.span {(M : ↥(Ohat F))}) => x i j) (MonoidHom.mem_ker.1 hg)
    change Ideal.Quotient.mk _ (g i j) = (1 : Matrix (Fin n) (Fin n) _) i j at h1
    change Ideal.Quotient.mk _ ((1 : Matrix (Fin n) (Fin n) (Ohat F)) i j -
      eLoc w ((1 : Matrix (Fin n) (Fin n) (Ohat F)) i j) + eLoc w (g i j)) = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [eLoc_eq w (g i j), eLoc_eq w (_ : Ohat F)]
    simp [h1, Matrix.one_apply, apply_ite (Ideal.Quotient.mk (Ideal.span {(M : ↥(Ohat F))}))]
  · ext i j : 2
    change ((1 : Matrix (Fin n) (Fin n) (Ohat F)) i j : Af F) -
      sLoc F w (pLoc F w ((1 : Matrix (Fin n) (Fin n) (Ohat F)) i j : Ohat F)) + sLoc F w (pLoc F w (g i j)) =
      (1 : Matrix (Fin n) (Fin n) (Af F)) i j - sLoc F w ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion F)) i j) +
        sLoc F w (pLoc F w (g i j))
    by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem tendsto_of_loc {α : Type} {𝓕 : Filter α} {f : α → Af F} {x : Af F} (hx : x ∈ Ohat F) (hf : ∀ᶠ a in 𝓕, f a ∈ Ohat F)
    (h : ∀ w, ∀ᶠ a in 𝓕, pLoc F w (f a) = pLoc F w x) : Tendsto f 𝓕 (𝓝 x) := by
  classical
  let s := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
  have hs : Continuous s := RestrictedProduct.isEmbedding_structureMap.continuous
  let lift : Af F → ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun y v => if h : y ∈ Ohat F then ⟨pLoc F v y, mem_Ohat.1 h v⟩ else ⟨0, zero_mem _⟩
  have hl : ∀ y ∈ Ohat F, s (lift y) = y := fun y hy => FiniteAdeleRing.ext _ fun v => by
    change ((lift y v : _) : v.adicCompletion F) = pLoc F v y
    simp [lift, hy]
  have h1 : Tendsto (fun a => lift (f a)) 𝓕 (𝓝 (lift x)) := tendsto_pi_nhds.2 fun v =>
    tendsto_const_nhds.congr' <| by
      filter_upwards [hf, h v] with a ha hav
      simp [lift, ha, hx, hav]
  have h2 := (hs.tendsto _).comp h1
  rw [hl x hx] at h2
  exact h2.congr' (hf.mono fun a ha => hl _ ha)

theorem entry_mem {k : GL (Fin n) (Af F)} (hk : k ∈ KLev F n M) (i j : Fin n) : k i j ∈ Ohat F := by
  obtain ⟨g, -, rfl⟩ := hk
  exact (g i j).2


variable (n M) in
noncomputable def KAway (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup (GL (Fin n) (Af F)) :=
  KLev F n M ⊓ ⨅ w ∈ S, (GeneralLinearGroup.map (pLoc F w)).ker

theorem mem_KAway {S : Finset (HeightOneSpectrum (𝓞 F))} {k : GL (Fin n) (Af F)} :
    k ∈ KAway n M S ↔ k ∈ KLev F n M ∧ ∀ w ∈ S, GeneralLinearGroup.map (pLoc F w) k = 1 := by
  simp [KAway, Subgroup.mem_iInf]

theorem exists_KAway_subset {U : Set (GL (Fin n) (Af F))} (hU : U ∈ 𝓝 (1 : GL (Fin n) (Af F))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), (KAway n M S : Set (GL (Fin n) (Af F))) ⊆ U := by
  classical
  by_contra hn
  push Not at hn
  choose k hk hkU using fun S => Set.not_subset.1 (hn S)
  have ent : ∀ k : Finset (HeightOneSpectrum (𝓞 F)) → GL (Fin n) (Af F), (∀ S, k S ∈ KAway n M S) →
      Tendsto (fun S => (k S).val) atTop (𝓝 1) := fun k hk =>
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j =>
      tendsto_of_loc (entry_mem (one_mem (KLev F n M)) i j) (.of_forall fun S => entry_mem (mem_KAway.1 (hk S)).1 i j) fun w => by
        filter_upwards [eventually_ge_atTop {w}] with S hS
        have e := (mem_KAway.1 (hk S)).2 w (hS (Finset.mem_singleton_self w))
        rw [← map_one (GeneralLinearGroup.map (pLoc F w))] at e
        exact congrArg (fun x : GL (Fin n) (w.adicCompletion F) => x i j) e
  have ht : Tendsto k atTop (𝓝 1) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    exact (ent k hk).prodMk_nhds
      ((MulOpposite.continuous_op.tendsto _).comp (ent (fun S => (k S)⁻¹) fun S => inv_mem (hk S)))
  obtain ⟨S, hS⟩ := (ht.eventually hU).exists
  exact hkU S hS

end UpperTheory.V.Af.GlobalFixedVectors

end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial

private theorem contCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem UpperTheory.V.Af.isoOfFrob :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.IsoOfFrob := by
  intro _ F Ω _ _ _ _ _ l _ ι n r r' hr hr' hs hs' hw
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hw)
  have hc : ∀ g : G F Ω, (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
    intro g
    ext i
    have h1 : Continuous fun g : G F Ω => (r g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr.comp continuous_inv))
    have h2 : Continuous fun g : G F Ω => (r' g⁻¹ : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff i :=
      (contCoeff n i).comp (Units.continuous_val.comp (hr'.comp continuous_inv))
    refine congrFun (Continuous.ext_on hD h1 h2 ?_) g
    rintro σ ⟨v, hv, -, A, hA, hσ⟩
    obtain ⟨B, hB, hB'⟩ := not_not.1 hv
    have h := ((hB A hA).2 σ hσ).trans ((hB' A hA).2 σ hσ).symm
    have h' := Polynomial.map_injective ι.toRingHom ι.injective h
    simp only [h']
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hs hs' (fun g => by simpa using hc g⁻¹)
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.JumpsAbove
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.GalOfCusp

namespace UpperTheory.V.Af.JumpsAbove

variable {l : ℕ} [Fact l.Prime]

private theorem char_mult (K L : FinExt l) (κ : ↥(GK K) →* (↥L.1)ˣ) (hκ : Continuous fun g => (κ g : ↥L.1)) (w : ℤ)
    (hw : Loc.HasWeight (GK K).subtype κ w) (hd : IsDR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ))
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (a : ℤ) : multV ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ a = if a = -w then 1 else 0 := by
  have := L.2
  have := K.2
  have : IsModuleTopology ℚ_[l] ↥L.1 := isModuleTopologyOfFiniteDimensional
  obtain ⟨T⟩ := Loc.tiedP l
  have hφ : Topology.IsOpenEmbedding (GK K).subtype :=
    (IntermediateField.fixingSubgroup_isOpen K.1).isOpenEmbedding_subtypeVal
  have h := (Loc.charFil (GK K).subtype hφ κ hκ w hw).2
  have hF : ∀ i, Loc.FilT ↥L.1 ↥L.1 i = FilV ((Loc.PP l).PD K) (LL := ↥L.1) (V := ↥L.1) i := fun i => by
    have : (((Loc.PP l).PD (Loc.botExt l)).Fil i).restrictScalars ℚ_[l] =
        (((Loc.PP l).PD K).Fil i).restrictScalars ℚ_[l] := SetLike.coe_injective ((Loc.PP l).PD_Fil _ _ i)
    unfold Loc.FilT FilV
    rw [this]
  have hD : Loc.Ddr (GK K).subtype (Loc.chRep κ) = DdR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) := by
    unfold Loc.Ddr DdR
    refine iInf_congr fun g => ?_
    have h2 : actVdR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) g = Loc.actD (GK K).subtype (Loc.chRep κ) g := by
      unfold actVdR Loc.actD
      congr 1
      exact LinearMap.ext fun z => (Loc.PP l).PD_actdR K g z
    rw [h2]
  simp only [Loc.FilD, hF, hD] at h
  have hr := (((GlobalTheory.Per.Components.components_finrank l _ _ T K L _ (Formalism.WeaklyAdmissibleFiltrations.charRep κ)).1 τ).2.2 hd).trans
    (Module.finrank_self _)
  have hle : DdRE ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ ≤ DdR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) := inf_le_left
  set_option synthInstance.maxHeartbeats 200000 in
  have h1 : ∀ i, i ≤ -w → Module.finrank ↥L.1 ↥(FildR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ i) = 1 := fun i hi => by
    rw [FildR, inf_eq_left.2 (hle.trans (inf_eq_left.1 ((h i).1 hi))), hr]
  set_option synthInstance.maxHeartbeats 200000 in
  have h0 : ∀ i, -w < i → Module.finrank ↥L.1 ↥(FildR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep κ) τ i) = 0 := fun i hi => by
    rw [FildR, le_bot_iff.1 ((inf_le_inf_right _ hle).trans ((h i).2 hi).le), finrank_bot]
  unfold multV
  rcases lt_trichotomy a (-w) with ha | ha | ha
  · rw [h1 a ha.le, h1 (a + 1) ha, if_neg ha.ne]; simp
  · rw [h1 a ha.le, h0 (a + 1) (by omega), if_pos ha]; simp
  · rw [h0 a ha, h0 (a + 1) (by omega), if_neg ha.ne']; simp

private theorem flag_mult (K L : FinExt l) (n : ℕ) : ∀ (ρ : Representation ↥L.1 ↥(GK K) (Fin n → ↥L.1))
    (M : ↥(GK K) → Matrix (Fin n) (Fin n) ↥L.1) (κ : Fin n → ↥(GK K) →* (↥L.1)ˣ),
    (∀ g x, ρ g x = (M g).mulVec x) → (∀ g i j, j < i → M g i j = 0) → (∀ g i, M g i i = κ i g) →
    IsDR ((Loc.PP l).PD K) ρ → (∀ i, IsDR ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep (κ i))) ∧
      ∀ τ a, multV ((Loc.PP l).PD K) ρ τ a = ∑ i, multV ((Loc.PP l).PD K) (Formalism.WeaklyAdmissibleFiltrations.charRep (κ i)) τ a := by
  obtain ⟨T⟩ := Loc.tiedP l
  induction n with
  | zero =>
    intro ρ M κ _ _ _ _
    refine ⟨fun i => i.elim0, fun τ a => ?_⟩
    have : Subsingleton (TensorProduct ℚ_[l] (Fin 0 → ↥L.1) (Loc.PP l).R.BdR) := inferInstance
    simp [multV, Module.finrank_zero_of_subsingleton]
  | succ n ih =>
    intro ρ M κ hρ hM hκ hd
    let ι : ↥L.1 →ₗ[↥L.1] (Fin (n + 1) → ↥L.1) := LinearMap.single _ (fun _ => ↥L.1) 0
    let π : (Fin (n + 1) → ↥L.1) →ₗ[↥L.1] (Fin n → ↥L.1) := LinearMap.funLeft _ _ Fin.succ
    let M' : ↥(GK K) → Matrix (Fin n) (Fin n) ↥L.1 := fun g => (M g).submatrix Fin.succ Fin.succ
    have hπ : ∀ g x, π (ρ g x) = (M' g).mulVec (π x) := fun g x => by
      funext i
      simp [π, M', hρ, LinearMap.funLeft_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        hM g i.succ 0 (Fin.succ_pos i)]
    have hs : Function.Surjective π := LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.succ_injective n)
    let ρ' : Representation ↥L.1 ↥(GK K) (Fin n → ↥L.1) :=
      { toFun := fun g => Matrix.toLin' (M' g)
        map_one' := LinearMap.ext fun y => by
          obtain ⟨x, rfl⟩ := hs y
          rw [Matrix.toLin'_apply, ← hπ, map_one]; rfl
        map_mul' := fun g h => LinearMap.ext fun y => by
          obtain ⟨x, rfl⟩ := hs y
          rw [Module.End.mul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, ← hπ, ← hπ, ← hπ,
            map_mul]; rfl }
    obtain ⟨d0, d2, hm⟩ := GlobalTheory.Per.ExactMult.exact_hodge_add l _ _ T K L _ (Formalism.WeaklyAdmissibleFiltrations.charRep (κ 0)) _ ρ _ ρ' ι π
      (fun g x => by
        funext i
        rw [hρ]
        refine Fin.cases ?_ (fun i => ?_) i
        · simp [ι, Formalism.WeaklyAdmissibleFiltrations.charRep, hκ]
        · simp [ι, Formalism.WeaklyAdmissibleFiltrations.charRep, hM g i.succ 0 (Fin.succ_pos i)])
      hπ (fun x y h => by simpa [ι] using congrFun h 0) hs
      (by
        ext x
        simp only [LinearMap.mem_range, LinearMap.mem_ker]
        constructor
        · rintro ⟨y, rfl⟩
          funext i
          simp [ι, π, LinearMap.funLeft_apply]
        · intro h
          refine ⟨x 0, funext fun i => Fin.cases ?_ (fun i => ?_) i⟩
          · simp [ι]
          · simpa [ι, π, LinearMap.funLeft_apply] using (congrFun h i).symm) hd
    obtain ⟨e1, e2⟩ := ih ρ' M' (fun i => κ i.succ) (fun g x => rfl)
      (fun g i j h => hM g _ _ (Fin.succ_lt_succ_iff.2 h)) (fun g i => hκ g _) d2
    refine ⟨fun i => Fin.cases d0 e1 i, fun τ a => ?_⟩
    rw [(hm τ a).2.1, Fin.sum_univ_succ, e2]

private theorem exists_open (K : FinExt l) {M : ℕ} (hM : 1 ≤ M) : ∃ U : Subgroup ↥(GK K), IsOpen (U : Set ↥(GK K)) ∧
    ∀ s ∈ U, ∀ ζ : Om l, ζ ^ M = 1 → (s : GQ l) ζ = ζ := by
  have : NeZero M := ⟨by omega⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) M
  have : FiniteDimensional ℚ_[l] ↥(IntermediateField.adjoin ℚ_[l] {z}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
  refine ⟨(IntermediateField.adjoin ℚ_[l] {z}).fixingSubgroup.comap (GK K).subtype,
    (IntermediateField.fixingSubgroup_isOpen _).preimage continuous_subtype_val, fun s hs ζ hζ => ?_⟩
  obtain ⟨i, -, rfl⟩ := hz.eq_pow_of_pow_eq_one hζ
  have h : (s : GQ l) z = z := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs z
    (IntermediateField.mem_adjoin_simple_self _ z)
  rw [map_pow, h]

end UpperTheory.V.Af.JumpsAbove

end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.KlevThree
section
private theorem klev_three (K : Type) [Field K] [NumberField K] (n M : ℕ) :
    UpperTheory.V.Af.KLev K n (3 * M) ≤ UpperTheory.V.Af.KLev K n M := by
  refine Subgroup.map_mono fun k hk => ?_
  have hle : Ideal.span {((3 * M : ℕ) : ↥(UpperTheory.V.Af.Ohat K))} ≤ Ideal.span {(M : ↥(UpperTheory.V.Af.Ohat K))} :=
    Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast (Dvd.intro_left 3 rfl))
  have e := congrArg (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.factor hle)) (MonoidHom.mem_ker.1 hk)
  rw [map_one] at e
  exact e
end

