module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0032
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0054
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0056
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.VacAll
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0055
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0033
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0051
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.CwInvIota
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0041
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingGrp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0028
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.PolynomialGaussianIntegrals.IntegralJnp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0043
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0057
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0031
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0042

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepCLawE
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem a_dil_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (i₀ : Fin d.n) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single i₀ 1) τ y) (h : d.G) : d.a (R.ι w y * h) = Real.exp (2 * τ) * d.a h ∧ 0 ≤ d.a h := by
  haveI := d.cm.1
  have hf := _root_.PositivityTheory.SiegelWeilFormula.AStep.inFrame_dil'_k R w i₀ τ y hy
  have h21 : (inFrame d.b (R.ι w y)).toBlocks₂₁ = 0 := by rw [hf, Matrix.toBlocks_fromBlocks₂₁]
  obtain ⟨t, ht, hdet⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.isPar_of_frame_k d (R.ι w y) h21
  have hdetU : Matrix.GeneralLinearGroup.det t = Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ) := by
    rw [← det_dilT d.cm w i₀ τ]
    apply Units.ext
    rw [hdet, hf, Matrix.toBlocks_fromBlocks₁₁]
    rfl
  refine ⟨?_, ?_⟩
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.a_mul_par_k d ht h, hdetU, absE_adrU d.cm w τ]
  · obtain ⟨p, tp, hp, k, hk, rfl⟩ := d.ok.hgt.iwa h
    rw [d.ok.hgt.val p tp hp k hk]
    exact NNReal.coe_nonneg _
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAtopVacAll
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Atop
open PositivityTheory.SiegelWeilFormula.KMain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.gens {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (s : Finset (InfinitePlace F)) : Set (Mx F E d.m d.n → ℂ) :=
  {f | ∃ (P : InfinitePlace F → PX d.m d.n) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ), (∀ w ∉ s, P w = 1) ∧ g ∈ SB _ ∧
    f = fun X => (∏ w, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2}
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.vacOn {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (s : Finset (InfinitePlace F)) : Submodule ℂ (Mx F E d.m d.n → ℂ) :=
  Submodule.span ℂ (R.gens s)
theorem vacOn_empty_le_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.vacOn ∅ ≤ R.vac := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨P, g, hP, hg, rfl⟩
  refine Submodule.subset_span ⟨g, hg, ?_⟩
  funext X
  simp only [hP _ (Finset.notMem_empty _)]
theorem fock_le_vacOn_univ_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.fock ≤ R.vacOn Finset.univ := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨P, g, hg, rfl⟩
  exact Submodule.subset_span ⟨P, g, fun w hw => absurd (Finset.mem_univ w) hw, hg, rfl⟩
theorem vacOn_step_k (hG : AbsSt.GenCore) (c : ℂ) (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hFM : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hLE : _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k)
    (hLo : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hGS : _root_.PositivityTheory.SiegelWeilFormula.GSplit_k) (hGI : _root_.PositivityTheory.SiegelWeilFormula.GIinv_k) (hGD : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hSK : _root_.PositivityTheory.SiegelWeilFormula.SecK_k)
    (hEW : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (s : Finset (InfinitePlace F)) (hw : w ∉ s)
    (ih : ∀ Φ ∈ d.sch, d.T Φ ∈ R.vacOn s → ∀ x,
      HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φ x)) :
    ∀ Φ ∈ d.sch, d.T Φ ∈ R.vacOn (insert w s) → ∀ x,
      HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φ x) := by
  have hgen : ∀ f ∈ R.gens (insert w s), ∃ Φf : d.Fn, d.KFin Φf ∧ d.T Φf = f ∧ ∀ x,
      HolValueAt (fun z => d.eis (d.sec0 Φf) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φf x) := by
    rintro f ⟨P, g, hP, hg, rfl⟩
    set Ψ : Mx F E d.m d.n → ℂ := fun X => (∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) *
      g fun k => (d.crd X k).2 with hΨdef
    have hΨ : Ψ ∈ R.away w := Submodule.subset_span ⟨P, g, hg, rfl⟩
    obtain ⟨φ, hφ⟩ := hLE F E σ d R w Ψ hΨ
    have hTP : ∀ Q : PX d.m d.n, d.T (φ Q) = fun X => (∏ w', fP (Function.update P w Q w') (R.loc w' X)) *
        g fun k => (d.crd X k).2 := by
      intro Q
      rw [(hφ Q).2]
      funext X
      simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hΨdef]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), Function.update_self, mul_assoc]
      congr 2
      refine Finset.prod_congr rfl fun w' hw' => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw')]
    have hfock : ∀ Q, d.T (φ Q) ∈ R.fock := fun Q => by
      rw [hTP Q]
      exact Submodule.subset_span ⟨_, g, hg, rfl⟩
    have hKF : ∀ Q, d.KFin (φ Q) := fun Q => hPK F E σ d R (φ Q) (hφ Q).1 (hfock Q)
    have hvac : ∀ x, HolValueAt (fun z => d.eis (d.sec0 (φ 1)) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I (φ 1) x) := by
      refine ih (φ 1) (hφ 1).1 ?_
      rw [hTP 1]
      refine Submodule.subset_span ⟨Function.update P w 1, g, fun w' hw' => ?_, hg, rfl⟩
      by_cases e : w' = w
      · subst e; exact Function.update_self _ _ _
      · rw [Function.update_of_ne e]
        exact hP w' (by simp [e, hw'])
    refine ⟨φ (P w), hKF (P w), ?_, _root_.PositivityTheory.SiegelWeilFormula.Atop.genAt_k hG c hT hAux hFM hLo hLI hGS hGI hGD hPK hSK hEW d R w hΨ hφ hvac (P w)⟩
    rw [hTP (P w), Function.update_eq_self]
  intro Φ hΦ hTΦ x
  obtain ⟨k, a, f, hf⟩ := Submodule.mem_span_set'.1 hTΦ
  choose Φf hK hTf hI using fun i => hgen (f i).1 (f i).2
  have hΦeq : Φ = ∑ i, a i • Φf i := by
    have hmem : Φ - ∑ i, a i • Φf i ∈ d.sch :=
      d.sch.sub_mem hΦ (d.sch.sum_mem fun i _ => d.sch.smul_mem _ (hK i).1)
    refine sub_eq_zero.mp ((hT.1 F E σ d).2.2 _ hmem ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, map_sub, map_sum]
    simp only [map_smul, _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, hTf, hf, sub_self]
  rw [hΦeq]
  exact _root_.PositivityTheory.SiegelWeilFormula.Atop.ident_lincomb_k hT hSK hEW d c a Φf hK hI x
end PositivityTheory.SiegelWeilFormula.Atop
namespace PositivityTheory.SiegelWeilFormula
def VacAllOfC_k : Prop :=
  AbsSt.GenCore → _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k → _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k → _root_.PositivityTheory.SiegelWeilFormula.LocInst_k → _root_.PositivityTheory.SiegelWeilFormula.GSplit_k → _root_.PositivityTheory.SiegelWeilFormula.GIinv_k → _root_.PositivityTheory.SiegelWeilFormula.GIdil_k → _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k → _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k →
    _root_.PositivityTheory.SiegelWeilFormula.SecK_k → _root_.PositivityTheory.SiegelWeilFormula.EisWk_k → _root_.PositivityTheory.SiegelWeilFormula.VacAll_k
theorem Atop.vacAllOfC_k : _root_.PositivityTheory.SiegelWeilFormula.VacAllOfC_k := by
  intro hG hT hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hEW F E _ _ _ _ _ σ d R c hV Φ hΦ x
  have claim : ∀ s : Finset (InfinitePlace F), ∀ Φ ∈ d.sch, d.T Φ ∈ R.vacOn s → ∀ x,
      HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φ x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun Φ hΦ hT x => hV Φ hΦ (_root_.PositivityTheory.SiegelWeilFormula.Atop.vacOn_empty_le_k R hT) x
    | insert w s hw ih => exact _root_.PositivityTheory.SiegelWeilFormula.Atop.vacOn_step_k hG c hT hAux hFM hLE hLo hLI hGS hGI hGD hPK hSK hEW d R w s hw ih
  exact claim Finset.univ Φ hΦ.1 (_root_.PositivityTheory.SiegelWeilFormula.Atop.fock_le_vacOn_univ_k R (hKP F E σ d R Φ hΦ)) x
end PositivityTheory.SiegelWeilFormula
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaEps
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem eps_eq_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : ∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 ∧
    L.b.1ᵀ * dbl L.Y.J * L.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  obtain ⟨ε', hε'⟩ := L.ok.frame.1
  have s := _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_sign_k d ε hε
  have s' := _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_sign_k L.sd ε' hε'
  refine ⟨ε, hε, ?_⟩
  suffices e : ε' = ε by rw [← e]; exact hε'
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩ <;> rcases L.ok.sign with ⟨hA', hY'⟩ | ⟨hA', hY'⟩
  · rw [s.1 hY, s'.1 hY']
  · exact (not_herm_skew d.ok.hm hA hA').elim
  · exact (not_herm_skew d.ok.hm hA' hA).elim
  · rw [s.2 hY, s'.2 hY']
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacKB
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics (mkGR inFrame_mul inFrame_one cw_mul cw_one form_w)
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem iota_vg_k (hO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (y : GR d.n) (hy : InK (mR y))
    {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ} {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hT : d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g) :
    ∃ c : ℂ, d.T (d.om (R.ι w y) Φ) = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R (c • g) := by
  obtain ⟨L, hL⟩ := hO F E σ d R w
  obtain ⟨sL, ρ, p, q, e, -, hld, -, hk⟩ := hI F E σ d R w L hL
  have h1 := (hL y _ _root_.PositivityTheory.SiegelWeilFormula.Avac.isSchwartz_fourierProjection_one).2 (_root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k R g w) (_root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_indep_k R g w) Φ hΦ (hT.trans (_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_tens_k R g w))
  refine ⟨F0 p q e y, ?_⟩
  rw [h1, hk y 1 hy, hld.kvac y hy, _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_tens_k R _ w]
  funext X
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, _root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k, Pi.smul_apply, smul_eq_mul, _root_.PositivityTheory.SiegelWeilFormula.Avac.fP_smul_one_k]
  ring
theorem dZ_conjT_k {ζ : ℂ} : (dZ d.n ζ)ᴴ = dZ d.n (star ζ) := by
  simp [dZ, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_smul]
theorem star_zeta_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : star R.ζ = R.ζ⁻¹ := by
  rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp
theorem kdec_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (k : d.G)
    (hk : d.cw w (inFrame d.b k) * (d.cw w (inFrame d.b k))ᴴ = 1) :
    ∃ y : GR d.n, InK (mR y) ∧ d.cw w (inFrame d.b (R.ι w y)) = d.cw w (inFrame d.b k) := by
  have hζ0 := Krd.zeta_ne R.hζ
  obtain ⟨M, hM⟩ : ∃ M, M = d.cw w (inFrame d.b k) := ⟨_, rfl⟩
  have hY := Krd.inG_conj R.hζ M (hM ▸ _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.form_w_k d R w k)
  have hMM : Mᴴ * M = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 (hM ▸ hk)
  refine ⟨mkGR _ hY, ⟨hY, ?_⟩, ?_⟩
  · show (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹)ᴴ * (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹) = 1
    have hA : (dZ d.n R.ζ)ᴴ = dZ d.n R.ζ⁻¹ := by rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.dZ_conjT_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.star_zeta_k]
    have hB : (dZ d.n R.ζ⁻¹)ᴴ = dZ d.n R.ζ := by rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.dZ_conjT_k, star_inv₀, _root_.PositivityTheory.SiegelWeilFormula.Avac.star_zeta_k, inv_inv]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hA, hB]
    calc dZ d.n R.ζ * (Mᴴ * dZ d.n R.ζ⁻¹) * (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹)
        = dZ d.n R.ζ * (Mᴴ * (dZ d.n R.ζ⁻¹ * dZ d.n R.ζ) * M) * dZ d.n R.ζ⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Krd.dZ_inv_mul hζ0, Matrix.mul_one, hMM, Matrix.mul_one, Krd.dZ_mul_inv hζ0]
  · rw [← hM]
    have h := R.at_w w (mkGR _ hY)
    calc d.cw w (inFrame d.b (R.ι w (mkGR _ hY)))
        = dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * d.cw w (inFrame d.b (R.ι w (mkGR _ hY)))) := by
          rw [← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]
      _ = dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹ * dZ d.n R.ζ) := by rw [h]; rfl
      _ = M := by
          simp only [Matrix.mul_assoc]
          rw [Krd.dZ_inv_mul hζ0, Matrix.mul_one, ← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]
theorem cw_inv_iota_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (y : GR d.n) (k : d.G) (w' : InfinitePlace F) :
    d.cw w' (inFrame d.b ((R.ι w y)⁻¹ * k)) = d.cw w' (inFrame d.b (R.ι w y)⁻¹) * d.cw w' (inFrame d.b k) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_mul_k]
theorem peel_k (hO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.FinAct_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (S : Finset (InfinitePlace F)) :
    ∀ k : d.G, (∀ w ∈ S, d.cw w (inFrame d.b k) * (d.cw w (inFrame d.b k))ᴴ = 1) →
      (∀ w ∉ S, d.cw w (inFrame d.b k) = 1) → ∀ g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F), ∀ Φ ∈ d.sch,
        d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g → ∃ g' ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F), d.T (d.om k Φ) = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g' := by
  induction S using Finset.induction_on with
  | empty =>
    intro k _ h1 g hg Φ hΦ hT
    obtain ⟨g', hg', H⟩ := hA F E σ d k (fun w => h1 w (Finset.notMem_empty w)) g hg
    exact ⟨g', hg', H _ (_root_.PositivityTheory.SiegelWeilFormula.Avac.gauss_indep_k R) Φ hΦ hT⟩
  | insert w S hw ih =>
    intro k h0 h1 g hg Φ hΦ hT
    obtain ⟨y, hy, hyw⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.kdec_k R w k (h0 w (Finset.mem_insert_self w S))
    have hinv : ∀ w', w' ≠ w → d.cw w' (inFrame d.b (R.ι w y)⁻¹) = 1 := fun w' h => by
      rw [← map_inv]; exact R.off_w w w' y⁻¹ h
    have e1 : d.cw w (inFrame d.b (R.ι w y)⁻¹) * d.cw w (inFrame d.b (R.ι w y)) = 1 := by
      rw [← _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_mul_k, ← _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.inFrame_mul_k, inv_mul_cancel, _root_.PositivityTheory.SiegelWeilFormula.Avac.inFrame_one_k, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_one_k]
    have hkw : d.cw w (inFrame d.b ((R.ι w y)⁻¹ * k)) = 1 := by rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.cw_inv_iota_k, ← hyw, e1]
    have hkw' : ∀ w', w' ≠ w → d.cw w' (inFrame d.b ((R.ι w y)⁻¹ * k)) = d.cw w' (inFrame d.b k) := fun w' h => by
      rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.cw_inv_iota_k, hinv w' h, Matrix.one_mul]
    obtain ⟨g₁, hg₁, e₁⟩ := ih ((R.ι w y)⁻¹ * k)
      (fun w' h => by
        rw [hkw' w' (fun e => hw (e ▸ h))]
        exact h0 w' (Finset.mem_insert_of_mem h))
      (fun w' h => by
        by_cases e : w' = w
        · rw [e, hkw]
        · rw [hkw' w' e]
          exact h1 w' fun h' => (Finset.mem_insert.1 h').elim e h)
      g hg Φ hΦ hT
    obtain ⟨c, e₂⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.iota_vg_k hO hI R w y hy (d.ok.dbl.weil.2.1.pres _ Φ hΦ) e₁
    refine ⟨c • g₁, Submodule.smul_mem _ c hg₁, ?_⟩
    rw [show k = R.ι w y * ((R.ι w y)⁻¹ * k) from (mul_inv_cancel_left _ _).symm, map_mul, Module.End.mul_apply]
    exact e₂
theorem vg_K'_k (hO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.FinAct_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
    {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ} (hg : g ∈ SB _) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hT : d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g)
    {k : d.G} (hk : k ∈ d.K) : ∃ g' ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F), d.T (d.om k Φ) = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g' :=
  _root_.PositivityTheory.SiegelWeilFormula.Avac.peel_k hO hI hA R Finset.univ k (fun w _ => ((d.ok.stdK k).1 hk).1 w) (fun w h => absurd (Finset.mem_univ w) h) g hg Φ hΦ hT
theorem vac_K'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.FinAct_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∀ k ∈ d.K, d.T (d.om k Φ) ∈ R.vac := by
  let S' : Submodule ℂ d.Fn :=
    { carrier := {Φ | Φ ∈ d.sch ∧ ∀ k ∈ d.K, d.T (d.om k Φ) ∈ R.vac}
      zero_mem' := ⟨zero_mem _, fun k _ => by
        rw [map_zero]
        have : d.T 0 = 0 := (_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k d).map_zero
        rw [this]; exact zero_mem _⟩
      add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, fun k hk => by
        rw [map_add (f := _)]
        have : d.T (d.om k a + d.om k b) = d.T (d.om k a) + d.T (d.om k b) := (_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k d).map_add _ _
        rw [this]; exact add_mem (ha.2 k hk) (hb.2 k hk)⟩
      smul_mem' := fun c a ha => ⟨Submodule.smul_mem _ c ha.1, fun k hk => by
        rw [map_smul]
        have : d.T (c • d.om k a) = c • d.T (d.om k a) := (_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k d).map_smul _ _
        rw [this]; exact Submodule.smul_mem _ c (ha.2 k hk)⟩ }
  have hle : R.vac ≤ S'.map (_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k d) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    have hm : _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g ∈ d.schM := (hF F E σ d R).1 (_root_.PositivityTheory.SiegelWeilFormula.Avac.vac_le_fock_k R (_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_mem_k R hg))
    obtain ⟨Φ, hΦ, e⟩ := (hT.1 F E σ d).2.1 _ hm
    refine ⟨Φ, ⟨hΦ, fun k hk => ?_⟩, e⟩
    obtain ⟨g', hg', e'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_K'_k hO hI hA R hg hΦ e hk
    rw [e']; exact _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_mem_k R hg'
  intro Φ hΦ hv k hk
  obtain ⟨Φ', hΦ', e⟩ := hle hv
  have : Φ' = Φ := _root_.PositivityTheory.SiegelWeilFormula.Avac.T_inj_k hT.1 hΦ'.1 hΦ e
  rw [← this]
  exact hΦ'.2 k hk
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfinpolybNufH
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFPB
open PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem map_isHaar_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) [νf.IsAddHaarMeasure] :
    (Measure.map (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2) ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf)).IsAddHaarMeasure := by
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) :=
    inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : BorelSpace (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := Pi.borelSpace
  haveI : MeasurableAdd (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := inferInstance
  haveI : SigmaFinite νf := inferInstance
  haveI : ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  exact ContinuousAddEquiv.isAddHaarMeasure_map ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf) (_root_.PositivityTheory.SiegelWeilFormula.KFPB.jnpE_k R)
theorem exists_nuf'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : ∃ νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), νf.IsAddHaarMeasure ∧
    (Measure.map (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2) ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf)).IsAddHaarMeasure := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  exact ⟨Measure.addHaar, inferInstance, _root_.PositivityTheory.SiegelWeilFormula.KFPB.map_isHaar_k R _⟩
theorem integral_jnp'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)} (hνf : νf.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) {g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ} (hg' : g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) {b : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → ℂ} (hb : Continuous b) (hb1 : ∀ u, ‖b u‖ ≤ 1) :
    ∫ X, f X * star (b (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) * g (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X))
        ∂(Measure.map (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2) ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf)) =
      ∫ u, star (b u) * _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf f g u := by
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) :=
    inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : BorelSpace (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := Pi.borelSpace
  haveI : SigmaFinite νf := inferInstance
  set μ := (volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf with hμ
  let e : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d ≃ᵐ Mx F E d.m d.n := (_root_.PositivityTheory.SiegelWeilFormula.KFPB.jnpE_k R).toHomeomorph.toMeasurableEquiv
  have hmap : Measure.map (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2) μ = Measure.map e μ := rfl
  have hH : (Measure.map e μ).IsAddHaarMeasure := _root_.PositivityTheory.SiegelWeilFormula.KFPB.map_isHaar_k R νf
  have hfi : Integrable (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => f (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2)) μ :=
    (integrable_map_equiv e f).1 (_root_.PositivityTheory.SiegelWeilFormula.KFock.int_schM_k d _ hH hf)
  obtain ⟨C, hC⟩ := hg'.1.continuous.bounded_above_of_compact_support hg'.2
  have hint : Integrable (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => f (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2) * star (b p.1 * g p.2)) μ := by
    refine hfi.mul_bdd (c := C) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (continuous_star.comp ((hb.comp continuous_fst).mul (hg'.1.continuous.comp continuous_snd))).aestronglyMeasurable
    · rw [norm_star, norm_mul]
      calc ‖b p.1‖ * ‖g p.2‖ ≤ 1 * C := mul_le_mul (hb1 _) (hC _) (norm_nonneg _) zero_le_one
        _ = C := one_mul C
  rw [hmap, integral_map_equiv]
  have he : ∀ p, e p = _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2 := fun p => rfl
  simp only [he, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_jn_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_jn_k]
  rw [integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k, star_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring
end PositivityTheory.SiegelWeilFormula.KFPB
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockFock
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem fockMem_k : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k := by
  intro F E _ _ _ _ _ σ d R
  exact ⟨_root_.PositivityTheory.SiegelWeilFormula.KFock.fock_le_k d R, fun w Ψ hΨ => ⟨fun P => _root_.PositivityTheory.SiegelWeilFormula.KFock.away_tens_k R w Ψ hΨ P, _root_.PositivityTheory.SiegelWeilFormula.KFock.away_inv_k R w Ψ hΨ⟩, fun w f hf => _root_.PositivityTheory.SiegelWeilFormula.KFock.fock_dec_k R w f hf⟩
theorem T_sub_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ Φ' : d.Fn) : d.T (Φ - Φ') = d.T Φ - d.T Φ' := by
  have h := _root_.PositivityTheory.SiegelWeilFormula.KFock.T_add_k d (Φ - Φ') Φ'
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm
theorem T_inj_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Φ Φ' : d.Fn} (h : Φ ∈ d.sch) (h' : Φ' ∈ d.sch) (e : d.T Φ = d.T Φ') : Φ = Φ' :=
  sub_eq_zero.mp ((hB F E σ d).2.2 _ (d.sch.sub_mem h h') (by rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.T_sub_k, e, sub_self]))
theorem linLift_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {V : Type} [AddCommGroup V] [Module ℂ V] (t : V →ₗ[ℂ] (Mx F E d.m d.n → ℂ))
    (ht : ∀ v, t v ∈ d.schM) : ∃ φ : V →ₗ[ℂ] d.Fn, ∀ v, φ v ∈ d.sch ∧ d.T (φ v) = t v := by
  choose φ0 hφ0 using fun v => (hB F E σ d).2.1 (t v) (ht v)
  refine ⟨{ toFun := φ0, map_add' := fun v v' => ?_, map_smul' := fun a v => ?_ }, fun v => hφ0 v⟩
  · refine _root_.PositivityTheory.SiegelWeilFormula.KFock.T_inj_k hB d (hφ0 (v + v')).1 (d.sch.add_mem (hφ0 v).1 (hφ0 v').1) ?_
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.T_add_k, (hφ0 _).2, (hφ0 _).2, (hφ0 _).2, map_add (f := _)]
  · refine _root_.PositivityTheory.SiegelWeilFormula.KFock.T_inj_k hB d (hφ0 (a • v)).1 (d.sch.smul_mem a (hφ0 v).1) ?_
    rw [RingHom.id_apply, _root_.PositivityTheory.SiegelWeilFormula.KFock.T_smul_k, (hφ0 _).2, (hφ0 _).2, map_smul]
def tensP_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) : PX d.m d.n →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun P := R.tens w (fP P) Ψ
  map_add' P Q := by
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, fP_add, Pi.add_apply, add_mul]
  map_smul' a P := by
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, fP_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
theorem liftEx_of_k : _root_.PositivityTheory.SiegelWeilFormula.TBij_k → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k := by
  intro hB hF F E _ _ _ _ _ σ d R w Ψ hΨ
  obtain ⟨φ, hφ⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.linLift_k hB d (_root_.PositivityTheory.SiegelWeilFormula.KFock.tensP_k R w Ψ) fun P => (hF F E σ d R).1 (((hF F E σ d R).2.1 w Ψ hΨ).1 P)
  exact ⟨φ, hφ⟩
theorem liftEx_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) : _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k := _root_.PositivityTheory.SiegelWeilFormula.KFock.liftEx_of_k hB _root_.PositivityTheory.SiegelWeilFormula.KFock.fockMem_k
theorem liftSw1_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (hf : IsSw f)
    (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) : ∃ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ :=
  (hB F E σ d).2.1 _ (_root_.PositivityTheory.SiegelWeilFormula.KFock.tens_mem_k d R w f hf Ψ hΨ)
end PositivityTheory.SiegelWeilFormula.KFock
end
end
end

