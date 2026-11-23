module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1829
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0049
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0024
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0073
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0020
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.SubMulRight
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0046
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0075
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0055
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FiniteLineActions.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0043
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0042
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0067

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RestrictCoreK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.DblTargetRestrictCore
open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF in
theorem restrict_core_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle)
        (ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ)),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
          Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
          (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (h : Formalism.IndefR.DatumF.GAF σ JT) (hd : Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)),
        Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) hd =
          Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.IndefR.DatumF.mtF σ JT h) 0 0 1) →
      ∀ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ → Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ →
        ωd (1, hd) (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) = GlobalTheory.DblTargetDelta.deltaT (ω (1, h) f₁) f₂ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ χS χT ω hω ωd hωd h hd hhd f₁ f₂ hf₁ hf₂
  obtain ⟨ι, hιc, hιm, hιq, hιs, hιd⟩ := _root_.GlobalTheory.DiagEmbU.exists_diagEmb F E σ nT JT
  have ext : ∀ a b : GAF σ (dblG JT), mtF σ (dblG JT) a = mtF σ (dblG JT) b → a = b := fun a b hab =>
    (HR (AF F) σ (dblG JT)).subtype_injective (Units.ext hab)
  have hdι : hd = ι h := ext _ _ (by rw [hhd, hιm])
  subst hdι
  have hsc := fun h' => _root_.GlobalTheory.T.weil_pair_global_character F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ χS χT ω hω ωd hωd h' (ι h') (hιm h')
  choose c hc1 hc using hsc
  have hth := _root_.GlobalTheory.T.theta_inner_product_formula F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ
  by_cases h0 : ∃ f₀, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ ≠ 0
  swap
  · push_neg at h0
    rw [h0 f₁ hf₁]
    have hz : ∀ g : WOF F E nS nT → ℂ, deltaT (0 : WOF F E nS nT → ℂ) g = 0 := fun g => by
      funext x; simp [deltaT]
    simp only [map_zero, hz]
  obtain ⟨f₀, hf₀, hf₀0⟩ := h0
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hf₀0
  set fs := heisOF σ JS JT ξ₀ B.ψ y f₀ with hfs
  have hfsθ : IsThetaFunOF σ JS JT ξ₀ B.ψ fs := _root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS nT JS JT ξ₀ y f₀ hf₀
  have hfs0 : fs 0 ≠ 0 := by
    have : symplOHF σ JS JT ξ₀ 0 y = 0 := by simp [symplOHF, symplOF, hOF]
    simp only [hfs, heisOF, this, AddChar.map_zero_eq_one, one_mul, zero_add]
    exact hy
  have top0 : topR (0 : WOF F E nS (nT + nT)) = 0 := by ext i j; rfl
  have bot0 : botR (0 : WOF F E nS (nT + nT)) = 0 := by ext i j; rfl
  have dl0 : ∀ a b : WOF F E nS nT → ℂ, deltaT a b 0 = a 0 * conj (b 0) := fun a b => by
    rw [deltaT_apply, top0, bot0, neg_zero]
  have hfsn : fs 0 * conj (fs 0) ≠ 0 := mul_ne_zero hfs0 ((map_ne_zero _).2 hfs0)
  have omi : ∀ h' : GAF σ JT, ω (1, h') (ω (1, h')⁻¹ fs) = fs := fun h' => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have pres := hω.om_pres
  have key : ∀ h' (a : ℂ), ωd (1, ι h') (deltaT (ω (1, h')⁻¹ fs) fs) 0 = a * (fs 0 * conj (fs 0)) → c h' = a := by
    intro h' a ha
    have e := congrFun (hc h' (ω (1, h')⁻¹ fs) fs (pres _ _ hfsθ) hfsθ) 0
    rw [Pi.smul_apply, smul_eq_mul, omi, dl0, ha] at e
    exact (mul_right_cancel₀ hfsn e).symm
  have hone : c 1 = 1 := by
    refine key 1 1 ?_
    have p1 : ((1 : GAF σ JS), (1 : GAF σ JT)) = 1 := rfl
    have p2 : ((1 : GAF σ JS), (1 : GAF σ (dblG JT))) = 1 := rfl
    rw [map_one, p1, p2, inv_one, map_one, map_one, Module.End.one_apply, Module.End.one_apply, dl0, one_mul]
  have hmul : ∀ a b, c (a * b) = c a * c b := by
    intro a b
    refine key (a * b) _ ?_
    have e1 : ((1 : GAF σ JS), ι (a * b)) = (1, ι a) * (1, ι b) := by rw [map_mul, Prod.mk_mul_mk, one_mul]
    set g := ω ((1 : GAF σ JS), a * b)⁻¹ fs with hg
    have hgθ : IsThetaFunOF σ JS JT ξ₀ B.ψ g := pres _ _ hfsθ
    have comb : ω (1, a) (ω (1, b) g) = fs := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, hg, omi]
    rw [e1, map_mul, Module.End.mul_apply, hc b g fs hgθ hfsθ, map_smul,
      hc a (ω (1, b) g) fs (pres _ _ hgθ) hfsθ, comb]
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, dl0]
    ring
  let cc : GAF σ JT →* Circle :=
    { toFun := fun h' => ⟨c h', mem_sphere_zero_iff_norm.2 (hc1 h')⟩
      map_one' := Circle.ext hone
      map_mul' := fun a b => Circle.ext (hmul a b) }
  have hcc : ∀ h', (cc h' : ℂ) = c h' := fun _ => rfl
  have hcont : Continuous cc := by
    refine continuous_induced_rng.2 (continuous_iff_continuousAt.2 fun h₀ => ?_)
    set g₁ := ω (1, h₀)⁻¹ fs
    have hg₁ : IsThetaFunOF σ JS JT ξ₀ B.ψ g₁ := pres _ _ hfsθ
    have hN : Continuous fun h' : GAF σ JT => ωd (1, ι h') (deltaT g₁ fs) 0 :=
      (hωd.om_cont _ (hth _ _ hg₁ hfsθ) 0).comp (continuous_const.prodMk hιc)
    have hD : Continuous fun h' : GAF σ JT => ω (1, h') g₁ 0 * conj (fs 0) :=
      ((hω.om_cont _ hg₁ 0).comp (continuous_const.prodMk continuous_id)).mul continuous_const
    have hD0 : ω (1, h₀) g₁ 0 * conj (fs 0) ≠ 0 := by rw [omi]; exact hfsn
    have hev : ∀ᶠ h' in nhds h₀, ω (1, h') g₁ 0 * conj (fs 0) ≠ 0 := hD.continuousAt.eventually_ne hD0
    refine ((hN.continuousAt).div hD.continuousAt hD0).congr (hev.mono fun h' hh' => ?_)
    show ωd (1, ι h') (deltaT g₁ fs) 0 / (ω (1, h') g₁ 0 * conj (fs 0)) = c h'
    rw [hc h' g₁ fs hg₁ hfsθ, Pi.smul_apply, smul_eq_mul, dl0, mul_div_assoc, div_self hh', mul_one]
  have hrat : ∀ γ ∈ GQF σ JT, cc γ = 1 := by
    intro γ hγ
    apply Circle.ext
    rw [hcc, Circle.coe_one]
    have e1 := hωd.om_aut 1 (Subgroup.one_mem _) (ι γ) (hιq γ hγ) _ (hth _ _ hfsθ hfsθ)
    have e2 := hω.om_aut 1 (Subgroup.one_mem _) γ hγ fs hfsθ
    rw [hc γ fs fs hfsθ hfsθ, Pi.smul_apply, smul_eq_mul, dl0, dl0, e2] at e1
    have := mul_right_cancel₀ hfsn (e1.trans (one_mul _).symm)
    exact this
  have hsplit : ∀ e, IsSplitIdemF σ e → ∀ g, SuppAtF σ e JT g → cc g = 1 := by
    intro e he g hg
    have hee : e * e = e := he.1
    obtain ⟨y, hy⟩ : ∃ y : (AEF F E)ˣ, IsDetAtF σ e JT g y := by
      have hd1 : (mtF σ JT g).det * ((Matrix.GeneralLinearGroup.det (matHomF σ JT g))⁻¹ : (AEF F E)ˣ) = 1 :=
        (Matrix.GeneralLinearGroup.det (matHomF σ JT g)).mul_inv
      have hd2 : ((Matrix.GeneralLinearGroup.det (matHomF σ JT g))⁻¹ : (AEF F E)ˣ) * (mtF σ JT g).det = 1 :=
        (Matrix.GeneralLinearGroup.det (matHomF σ JT g)).inv_mul
      refine ⟨⟨e * (mtF σ JT g).det + (1 - e),
        e * ((Matrix.GeneralLinearGroup.det (matHomF σ JT g))⁻¹ : (AEF F E)ˣ) + (1 - e), ?_, ?_⟩, rfl⟩
      · linear_combination ((mtF σ JT g).det * ((Matrix.GeneralLinearGroup.det (matHomF σ JT g))⁻¹ : (AEF F E)ˣ)
          - (mtF σ JT g).det - ((Matrix.GeneralLinearGroup.det (matHomF σ JT g))⁻¹ : (AEF F E)ˣ) + 1) * hee + e * hd1
      · linear_combination ((mtF σ JT g).det * ((Matrix.GeneralLinearGroup.det (matHomF σ JT g))⁻¹ : (AEF F E)ˣ)
          - (mtF σ JT g).det - ((Matrix.GeneralLinearGroup.det (matHomF σ JT g))⁻¹ : (AEF F E)ˣ) + 1) * hee + e * hd2
    have m1 : mtF σ JS (1 : GAF σ JS) = 1 := by unfold mtF; rw [map_one]; rfl
    have hx1 : IsDetAtF σ e JS 1 1 := by
      show ((1 : (AEF F E)ˣ) : AEF F E) = e * (mtF σ JS 1).det + (1 - e)
      rw [m1, Matrix.det_one, Units.val_one]; ring
    have hS1 : SuppAtF σ e JS 1 := fun i j => by rw [m1, sub_self]; simp
    obtain ⟨rd, hrd, hrd'⟩ := hωd.om_split e he 1 (ι g) hS1 (hιs e g hg) 1 y hx1 (hιd e g y hy)
    obtain ⟨r, hr, hr'⟩ := hω.om_split e he 1 g hS1 hg 1 y hx1 hy
    obtain ⟨ℓ, hℓ, a, b, ha, hb, hℓab⟩ := _root_.GlobalTheory.T.exists_split_functional_doubled F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he
    have hheis := _root_.GlobalTheory.T.theta_doubling_inner_product F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ
    have dadd : ∀ f f' : WOF F E nS nT → ℂ, deltaT (f + f') b = deltaT f b + deltaT f' b := fun f f' => by
      funext x; simp only [deltaT_apply, Pi.add_apply, add_mul]
    have dsmul : ∀ (s : ℂ) (f : WOF F E nS nT → ℂ), deltaT (s • f) b = s • deltaT f b := fun s f => by
      funext x; simp only [deltaT_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    let ℓ₁ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun f => ℓ (deltaT f b)
        map_add' := fun f f' => by simp only [dadd, map_add (f := _)]
        map_smul' := fun s f => by simp only [dsmul, map_smul, RingHom.id_apply] }
    have hℓ₁ : ∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
        ℓ₁ (heisOF σ JS JT ξ₀ B.ψ u f) = ℓ₁ f := by
      intro u hu f hf
      let ũ : WOF F E nS (nT + nT) := (Matrix.fromRows u 0).submatrix finSumFinEquiv.symm id
      have ht : topR ũ = u := by
        ext i j
        simp only [ũ, topR, Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply,
          Matrix.fromRows_apply_inl, id]
      have hb0 : botR ũ = 0 := by
        ext i j
        simp only [ũ, botR, Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply,
          Matrix.fromRows_apply_inr, Matrix.zero_apply, id]
      have hu' : ∀ i j, cAF σ e * ũ i j = ũ i j := by
        intro i j
        obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
        rcases i with i | i <;>
          simp only [ũ, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl,
            Matrix.fromRows_apply_inr, Matrix.zero_apply, mul_zero, id, hu]
      have h0b : heisOF σ JS JT ξ₀ B.ψ 0 b = b := by
        funext x; simp [heisOF, symplOHF, symplOF, hOF]
      show ℓ (deltaT (heisOF σ JS JT ξ₀ B.ψ u f) b) = ℓ (deltaT f b)
      have e3 := hheis ũ f b
      rw [ht, hb0, neg_zero, h0b] at e3
      rw [← e3, hℓ ũ hu' _ (hth f b hf hb)]
    have E1 := hrd' ℓ hℓ _ (hth a b ha hb)
    rw [hc g a b ha hb, map_smul, smul_eq_mul] at E1
    have E2 : ℓ (deltaT (ω (1, g) a) b) = (r : ℂ) * (splitFacOF χS χT 1 y : ℂ) * ℓ (deltaT a b) := hr' ℓ₁ hℓ₁ a ha
    have s1 : (splitFacOF χS χT 1 y : ℂ) = χS y := by simp [splitFacOF]
    have s2 : (splitFacOF χS 1 1 y : ℂ) = χS y := by simp [splitFacOF]
    rw [E2, s1] at E1
    rw [s2] at E1
    have hs : (χS y : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have hcr : c g * r = rd :=
      mul_right_cancel₀ (mul_ne_zero hs hℓab) (by linear_combination E1)
    have hcg : c g = ((rd / r : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, eq_div_iff (by exact_mod_cast hr.ne'), hcr]
    have hn := hc1 g
    rw [hcg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hrd hr)] at hn
    apply Circle.ext
    rw [hcc, Circle.coe_one, hcg, hn, Complex.ofReal_one]
  have hall := _root_.GlobalTheory.T.unitary_character_trivial_of_local F E σ B hB nT JT hT cc hcont hrat hsplit h
  rw [hc h f₁ f₂ hf₁ hf₂, ← hcc, hall, Circle.coe_one, one_smul]
end GlobalTheory.DblTargetRestrictCore
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaF
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem frame_formE_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ)
    (h : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) = Jm d.n ((ε : ℤ) : AE F E) := by
  have e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ) := by
    ext i j
    simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]
  have e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
    simp [dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]
  have key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) =
      (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  rw [e1, e2, ← key, h]
  ext (i | i) (j | j)
  · simp [incM, Jm]
  · by_cases hij : i = j
    · subst hij; simp [incM, Jm]
    · simp [incM, Jm, Matrix.one_apply_ne hij]
  · by_cases hij : i = j
    · subst hij; simp [incM, Jm, map_intCast]
    · simp [incM, Jm, Matrix.one_apply_ne hij]
  · simp [incM, Jm]
theorem sub_form_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (c : AE F E →+* AE F E) (ε : AE F E)
    (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (hr : ∀ b, b ≠ Sum.inr L.i₀ → M (Sum.inr L.i₀) b = 0) :
    (M.submatrix (Sum.map L.em L.em) (Sum.map L.em L.em))ᵀ * Jm L.n ε *
        (M.submatrix (Sum.map L.em L.em) (Sum.map L.em L.em)).map c =
      (Mᵀ * Jm d.n ε * M.map c).submatrix (Sum.map L.em L.em) (Sum.map L.em L.em) := by
  ext x y
  rw [Matrix.submatrix_apply, form_apply, form_apply]
  have hx : Sum.map L.em L.em x ≠ Sum.inr L.i₀ := by
    rcases x with x | x
    · simp
    · simpa using (L.rng (L.em x)).2 ⟨x, rfl⟩
  have hy : Sum.map L.em L.em y ≠ Sum.inr L.i₀ := by
    rcases y with y | y
    · simp
    · simpa using (L.rng (L.em y)).2 ⟨y, rfl⟩
  refine Fintype.sum_of_injective L.em L.inj _ _ (fun k hk => ?_) (fun k => rfl)
  have : k = L.i₀ := by by_contra h; exact hk ((L.rng k).1 h)
  subst this
  rw [hr _ hx, hr _ hy, map_zero]; ring
theorem sub_J_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (ε : AE F E) :
    (Jm d.n ε).submatrix (Sum.map L.em L.em) (Sum.map L.em L.em) = Jm L.n ε := by
  ext (i | i) (j | j) <;> simp [Jm, Matrix.one_apply, L.inj.eq_iff]
theorem mkG_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ)
    (hf : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) = Jm d.n ((ε : ℤ) : AE F E))
    (N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (hN : Nᵀ * Jm d.n ((ε : ℤ) : AE F E) * N.map (cA σ).toRingHom = Jm d.n ((ε : ℤ) : AE F E)) :
    ∃ g : d.G, inFrame d.b g = N := by
  set J := Jm d.n ((ε : ℤ) : AE F E) with hJdef
  have hNu : IsUnit N.det := by
    have e : Nᵀ * (J * N.map (cA σ).toRingHom * (((ε : ℤ) : AE F E) • J)) = 1 := by
      calc Nᵀ * (J * N.map (cA σ).toRingHom * (((ε : ℤ) : AE F E) • J))
          = (Nᵀ * J * N.map (cA σ).toRingHom) * (((ε : ℤ) : AE F E) • J) := by simp only [Matrix.mul_assoc]
        _ = J * (((ε : ℤ) : AE F E) • J) := by rw [hN]
        _ = 1 := Jm_sq d.n ε
    have := congrArg Matrix.det e
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    exact isUnit_iff_exists_inv.2 ⟨_, this⟩
  have hBm : IsUnit (incM F d.b.1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d, Matrix.det_one]⟩)
  have hBi : IsUnit (incM F (d.b⁻¹).1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.det_one]⟩)
  have hM0u : IsUnit (incM F d.b.1 * N * incM F (d.b⁻¹).1) :=
    (hBm.mul ((Matrix.isUnit_iff_isUnit_det _).2 hNu)).mul hBi
  have hf' : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom = J := hf
  rw [← hf'] at hN
  have hM0mem := KWhit.form_conj_out (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hN
  let u : GL (Fin d.n ⊕ Fin d.n) (AE F E) := hM0u.unit
  have hu : (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) =
      incM F d.b.1 * N * incM F (d.b⁻¹).1 := IsUnit.unit_spec hM0u
  have hmem : u ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
    show (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))ᵀ * dbl (incM F d.Y.J) *
      (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).map (cA σ) = dbl (incM F d.Y.J)
    rw [hu]
    exact hM0mem
  refine ⟨⟨u, hmem⟩, ?_⟩
  show incM F (d.b⁻¹).1 * (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) * incM F d.b.1 = N
  rw [hu]
  simp only [← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.one_mul]
  rw [Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.mul_one]
theorem q_split'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (ε : ℤˣ)
    (hd : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hL : L.b.1ᵀ * dbl L.Y.J * L.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (p : d.G) (lam : (AE F E)ˣ)
    (hp : ∀ a, inFrame d.b p a (Sum.inl L.i₀) = if a = Sum.inl L.i₀ then (lam : AE F E) else 0) :
    ∃ g : L.sd.G, IsQ F E L.i₀ (inFrame d.b (p * (L.j g)⁻¹)) lam := by
  set M := inFrame d.b p with hMdef
  have hfd := _root_.PositivityTheory.SiegelWeilFormula.Avac.frame_formE_k d ε hd
  have hfL := _root_.PositivityTheory.SiegelWeilFormula.Avac.frame_formE_k L.sd ε hL
  have hMform : Mᵀ * Jm d.n ((ε : ℤ) : AE F E) * M.map (cA σ).toRingHom = Jm d.n ((ε : ℤ) : AE F E) := by
    have hP : (mat2 p)ᵀ * dbl (incM F d.Y.J) * (mat2 p).map (cA σ).toRingHom = dbl (incM F d.Y.J) := p.2
    have := KWhit.form_conj_in (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hP
    have hfd' : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom =
        Jm d.n ((ε : ℤ) : AE F E) := hfd
    rw [hfd'] at this
    exact this
  have hrow := row_zero (cA σ).toRingHom ε hMform hp
  have hsub := _root_.PositivityTheory.SiegelWeilFormula.Avac.sub_form_k L (cA σ).toRingHom (((ε : ℤ) : AE F E)) M hrow
  rw [hMform, _root_.PositivityTheory.SiegelWeilFormula.Avac.sub_J_k] at hsub
  obtain ⟨g, hg⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.mkG_k L.sd ε hfL _ hsub
  refine ⟨g, ?_⟩
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, ← map_inv]
  set H' := inFrame d.b (L.j g⁻¹) with hH'
  have hI : IdI (I0 L.i₀) H' := _root_.PositivityTheory.SiegelWeilFormula.Avac.idI_j_k L g⁻¹
  have hsubH : H'.submatrix (Sum.map L.em L.em) (Sum.map L.em L.em) = inFrame L.b g⁻¹ := L.j_in g⁻¹
  have hinv : M.submatrix (Sum.map L.em L.em) (Sum.map L.em L.em) * inFrame L.b g⁻¹ = 1 := by
    have e := _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k L.sd g g⁻¹
    rw [mul_inv_cancel, _root_.PositivityTheory.SiegelWeilFormula.Avac.inFrame_one_k] at e
    rw [← hg]; exact e.symm
  refine ⟨fun a b ha hb => ?_, fun a => ?_, fun b hb => ?_⟩
  · obtain ⟨a', rfl⟩ := (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L a).1 ha
    obtain ⟨b', rfl⟩ := (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L b).1 hb
    have e := congrFun (congrFun (hI.sub_mul_right M (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_inj_k L) (_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_rng_k L)) a') b'
    rw [Matrix.submatrix_apply, hsubH, hinv] at e
    rw [e]
    by_cases hab : a' = b'
    · subst hab; simp
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne ((_root_.PositivityTheory.SiegelWeilFormula.Avac.emm_inj_k L).ne hab)]
  · rw [mul_col_one (fun v => (hI _ (Or.inl rfl) v).2)]
    exact hp a
  · rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr L.i₀)]
    · rw [(hI _ (Or.inr rfl) b).1, Matrix.one_apply_ne (Ne.symm hb), mul_zero]
    · intro c _ hc
      rw [show inFrame d.b p (Sum.inr L.i₀) c = 0 from hrow c hc, zero_mul]
    · simp
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKKfpGeoRot
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem cw_mul'_k (w : InfinitePlace F) {p q r : Type} [Fintype q] (A : Matrix p q (AE F E)) (B : Matrix q r (AE F E)) :
    d.cw w (A * B) = d.cw w A * d.cw w B := Matrix.map_mul
theorem cw_add'_k (w : InfinitePlace F) {p q : Type} (A B : Matrix p q (AE F E)) :
    d.cw w (A + B) = d.cw w A + d.cw w B := Matrix.map_add _ (map_add _) A B
theorem cw_one'_k (w : InfinitePlace F) : d.cw w (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)
theorem cw_transpose'_k (w : InfinitePlace F) {p q : Type} (A : Matrix p q (AE F E)) : d.cw w Aᵀ = (d.cw w A)ᵀ := rfl
theorem incM_b_mul_inv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : incM F (d.b : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) *
    incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) = 1 := by
  rw [incM, incM, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
theorem incM_b_inv_mul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) :
    incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) *
      incM F (d.b : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) = 1 := by
  rw [incM, incM, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
theorem inFrame_mul'_k (x y : d.G) : inFrame d.b (x * y) = inFrame d.b x * inFrame d.b y := by
  have e : mat2 (x * y) = mat2 x * mat2 y := rfl
  simp only [inFrame, e, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incM F (d.b : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)), _root_.PositivityTheory.SiegelWeilFormula.KFP.incM_b_mul_inv_k, Matrix.one_mul]
theorem inFrame_one'_k : inFrame d.b (1 : d.G) = 1 := by
  have e : mat2 (1 : d.G) = 1 := rfl
  simp only [inFrame, e, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.KFP.incM_b_inv_mul_k]
theorem matrixRep_eq_frameConj (x : d.G) : mat2 x = incM F (d.b : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) * inFrame d.b x *
    incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) := by
  simp only [inFrame, Matrix.mul_assoc]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.incM_b_mul_inv_k, Matrix.mul_one, ← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KFP.incM_b_mul_inv_k, Matrix.one_mul]
theorem cw_inFrame_prod'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (f : InfinitePlace F → GR d.n) (w' : InfinitePlace F) :
    ∀ L : List (InfinitePlace F), L.Nodup → d.cw w' (inFrame d.b ((L.map fun w => R.ι w (f w)).prod)) =
      if w' ∈ L then d.cw w' (inFrame d.b (R.ι w' (f w'))) else 1 := by
  intro L
  induction L with
  | nil => intro _; simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.inFrame_one'_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_one'_k]
  | cons a L ih =>
    intro hL
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, _root_.PositivityTheory.SiegelWeilFormula.KFP.inFrame_mul'_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_mul'_k, ih hL.2]
    by_cases h : w' = a
    · subst h
      simp [hL.1]
    · rw [R.off_w a w' (f a) h, Matrix.one_mul]
      simp [h]
theorem dZ_cw_rot'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (t : ℝ) (w : InfinitePlace F) :
    dZ d.n R.ζ * d.cw w (inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.KFP.rot_k R t)) = yrotM d.n (R.sg w) t * dZ d.n R.ζ := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.rot_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.cw_inFrame_prod'_k R (fun w => yrot d.n (R.sg w) t) w _ (Finset.nodup_toList _),
    if_pos (Finset.mem_toList.2 (Finset.mem_univ w)), R.at_w, mR_yrot]
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpRotVac
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
open Matrix
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem om_place_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hLO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) :
    ∃ (p q : ℕ) (e : ℤ), ∀ y : GR d.n, InK (mR y) → ∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∀ Ω ∈ d.sch, d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g →
      d.om (R.ι w y) Ω = F0 p q e y • Ω := by
  obtain ⟨L, hL⟩ := hLO F E σ d R w
  obtain ⟨sL, ρ, p, q, e, -, hLD, -, hLk⟩ := hLI F E σ d R w L hL
  refine ⟨p, q, e, fun y hy g hg Ω hΩ hTΩ => ?_⟩
  let Ψ : Mx F E d.m d.n → ℂ := fun X =>
    (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' X)) * g (fun k => (d.crd X k).2)
  have hΨ : Ψ ∈ R.away w := Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩
  have hvt : d.T Ω = R.tens w (fP (1 : PX d.m d.n)) Ψ := by
    rw [hTΩ]
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.gau_k, _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k, Ψ]
    rw [← Finset.mul_prod_erase Finset.univ (fun w' => fP (1 : PX d.m d.n) (R.loc w' X)) (Finset.mem_univ w), mul_assoc]
    rfl
  have h1 := (hL y (fP (1 : PX d.m d.n)) (KFock.isSw_fP 1)).2 Ψ (_root_.PositivityTheory.SiegelWeilFormula.KFock.away_inv_k R w Ψ hΨ) Ω hΩ hvt
  rw [hLk y 1 hy, hLD.kvac y hy] at h1
  have hfP : fP (F0 p q e y • (1 : PX d.m d.n)) = F0 p q e y • fP (1 : PX d.m d.n) := by
    funext u
    simp only [fP, evX, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, Pi.smul_apply, smul_eq_mul]
    ring
  have htens : R.tens w (F0 p q e y • fP (1 : PX d.m d.n)) Ψ = F0 p q e y • R.tens w (fP (1 : PX d.m d.n)) Ψ := by
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfP, htens, ← hvt, ← _root_.PositivityTheory.SiegelWeilFormula.KFock.T_smul_k] at h1
  have hS := d.ok.dbl.weil.2.1.toIsSplitting
  exact _root_.PositivityTheory.SiegelWeilFormula.KFock.T_inj_k hT.1 d (hS.pres _ Ω hΩ) (d.sch.smul_mem _ hΩ) h1
theorem om_rot_vac'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hLO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (t : ℝ) :
    ∃ χ : ℂ, χ ≠ 0 ∧ ∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∀ Ω ∈ d.sch, d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g → d.om (_root_.PositivityTheory.SiegelWeilFormula.KFP.rot_k R t) Ω = χ • Ω := by
  have key : ∀ l : List (InfinitePlace F), ∃ χ : ℂ, χ ≠ 0 ∧ ∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∀ Ω ∈ d.sch, d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g →
      d.om ((l.map fun w => R.ι w (yrot d.n (R.sg w) t)).prod) Ω = χ • Ω := by
    intro l
    induction l with
    | nil => exact ⟨1, one_ne_zero, fun g _ Ω _ _ => by simp⟩
    | cons w l ih =>
      obtain ⟨χ, hχ, h⟩ := ih
      obtain ⟨p, q, e, hw⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFP.om_place_k hT hLO hLI R w
      refine ⟨F0 p q e (yrot d.n (R.sg w) t) * χ, mul_ne_zero (weight_factor_rotation_ne_zero p q e d.n (R.sg w) t) hχ,
        fun g hg Ω hΩ hTΩ => ?_⟩
      have hK : InK (mR (yrot d.n (R.sg w) t)) := by rw [mR_yrot]; exact inK_yrotM' _ _ _
      rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, h g hg Ω hΩ hTΩ, map_smul,
        hw _ hK g hg Ω hΩ hTΩ, smul_smul, mul_comm]
  exact key _
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

