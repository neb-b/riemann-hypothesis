module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0010
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SiegelD
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1830
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1797
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.PartCharInvOf
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

namespace PositivityTheory.SiegelWeilFormula.Ald.PCI

theorem partCharInv_of (hfin : FinPart) : PartCharInv := by
  intro F _ _ ψ hψ κ' κ'' _ _ l hl hinv Ψ hΨ hzero
  classical
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.CharInvForm.exists_schwartz_one (κ'' → mixedEmbedding.mixedSpace F)
  obtain ⟨U₀, hU₀o, hU₀c, -, -⟩ := GlobalTheory.FinSepChar.finite_chars_separate F ψ hψ κ'' Set.univ Filter.univ_mem
  set θf : (κ'' → Af F) → ℂ := GlobalTheory.CharForm.cosetInd U₀ 0 with hθf
  have hθfSB : θf ∈ SB (κ'' → Af F) := GlobalTheory.CharForm.cosetInd_mem_SB U₀ hU₀o hU₀c 0
  have hθf0 : θf 0 = 1 := by simp [hθf, GlobalTheory.CharForm.cosetInd]
  set θ : (κ'' → AF F) → ℂ := pureA F f₀ θf with hθ
  let P : ((κ' ⊕ κ'' → AF F) → ℂ) →ₗ[ℂ] ((κ' ⊕ κ'' → AF F) → ℂ) :=
    { toFun := fun Φ x => Φ (Sum.elim (x ∘ Sum.inl) 0) * θ (x ∘ Sum.inr)
      map_add' := fun _ _ => by funext x; simp [add_mul]
      map_smul' := fun _ _ => by funext x; simp [mul_assoc] }
  have hP : ∀ Φ x, P Φ x = Φ (Sum.elim (x ∘ Sum.inl) 0) * θ (x ∘ Sum.inr) := fun _ _ => rfl
  have e1 : ∀ x : κ' ⊕ κ'' → AF F, (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((Sum.elim (x ∘ Sum.inl) 0 : κ' ⊕ κ'' → AF F) i).1) =
      Sum.elim ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) ∘ Sum.inl) 0 := by
    intro x; funext j; rcases j with j | j
    · rfl
    · simp only [Sum.elim_inr, Pi.zero_apply]
      exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have e2 : ∀ x : κ' ⊕ κ'' → AF F, (fun i => ((Sum.elim (x ∘ Sum.inl) 0 : κ' ⊕ κ'' → AF F) i).2) =
      Sum.elim ((fun i => (x i).2) ∘ Sum.inl) 0 := by
    intro x; funext j; rcases j with j | j <;> rfl
  have gen : ∀ (f : SchwartzMap (κ' ⊕ κ'' → mixedEmbedding.mixedSpace F) ℂ) (g : (κ' ⊕ κ'' → Af F) → ℂ),
      g ∈ SB (κ' ⊕ κ'' → Af F) → l (pureA F f g) = l (P (pureA F f g)) := by
    intro f g hg
    obtain ⟨fs, hfs⟩ := exists_slice (κ'' := κ'') f
    obtain ⟨f₁, hf₁⟩ := GlobalTheory.SchwartzBox.exists_schwartz_box fs f₀
    set g₁ : (κ' ⊕ κ'' → Af F) → ℂ := fun z => g (Sum.elim (z ∘ Sum.inl) 0) * θf (z ∘ Sum.inr) with hg₁def
    have hg₁ : g₁ ∈ SB (κ' ⊕ κ'' → Af F) := GlobalTheory.SchwartzBox.sb_box (sb_slice hg) hθfSB
    have hPf : P (pureA F f g) = pureA F f₁ g₁ := by
      funext x
      rw [hP]
      simp only [pureA, hθ, hf₁, hfs, hg₁def]
      rw [e1 x, e2 x]
      simp only [Function.comp_def]
      ring
    rw [hPf]
    obtain ⟨T, hT⟩ := hl g hg
    have hA : T f = T f₁ := by
      have h := arch_part T (fun L f₂ f₃ h23 => by
        obtain ⟨Y, hY⟩ := GlobalTheory.TraceDual.exists_trace_rep F κ'' L
        rw [← hT, ← hT, ← hinv (fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Y i)) 0)
          (pureA F f₂ g) (GlobalTheory.CharInvForm.mem_schA f₂ hg)]
        congr 1
        funext x
        simp only [pureA, h23, GlobalTheory.CharInvForm.psi_dot_inf hψ, hY, Function.comp_def, mul_assoc]) (f - f₁) (fun v hv => by
          have hv' : v = Sum.elim (v ∘ Sum.inl) 0 := by
            funext j; rcases j with j | j
            · rfl
            · exact congrFun hv j
          rw [SchwartzMap.sub_apply, hf₁, hfs, hv, hf₀, mul_one]
          rw [← hv', sub_self])
      rw [map_sub, sub_eq_zero] at h
      exact h
    let a : ((κ' ⊕ κ'' → Af F) → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun h => l (pureA F f₁ h)
        map_add' := fun h h' => by
          rw [← map_add (f := _)]
          congr 1
          funext x
          simp [pureA, add_mul, mul_assoc, mul_comm, mul_left_comm]
        map_smul' := fun s h => by
          rw [RingHom.id_apply, ← map_smul]
          congr 1
          funext x
          simp [pureA, add_mul, mul_assoc, mul_comm, mul_left_comm] }
    have hB : a g = a g₁ := by
      have h := hfin F ψ hψ κ' κ'' a (fun y h hh => by
        show l (pureA F f₁ _) = l (pureA F f₁ h)
        rw [← hinv (fun i => pairA F 0 (y i)) (pureA F f₁ h) (GlobalTheory.CharInvForm.mem_schA f₁ hh)]
        congr 1
        funext x
        simp [pureA, GlobalTheory.CharInvForm.dot_pairA_fin, Function.comp_def, mul_left_comm]) (g - g₁) (sub_mem hg hg₁) (fun z' => by
          simp only [Pi.sub_apply, hg₁def, Sum.elim_comp_inl, Sum.elim_comp_inr, hθf0, mul_one, sub_self])
      rw [map_sub, sub_eq_zero] at h
      exact h
    calc l (pureA F f g) = T f := hT f
      _ = T f₁ := hA
      _ = l (pureA F f₁ g) := (hT f₁).symm
      _ = a g := rfl
      _ = a g₁ := hB
      _ = l (pureA F f₁ g₁) := rfl
  have key : ∀ Φ ∈ schA F (κ' ⊕ κ''), l Φ = l (P Φ) := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem Φ hmem =>
      obtain ⟨f, g, hg, rfl⟩ := hmem
      exact gen f g hg
    | zero => simp
    | add _ _ _ _ h h' => rw [map_add (f := _), map_add (f := _), map_add (f := _), h, h']
    | smul c _ _ h => rw [map_smul, map_smul, map_smul, h]
  have h0 : P Ψ = 0 := by
    funext x
    rw [hP, hzero, zero_mul]
    rfl
  rw [key Ψ hΨ, h0, map_zero]

end PositivityTheory.SiegelWeilFormula.Ald.PCI

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Siegel
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F : Type} [Field F] [NumberField F]

theorem evalZero_mem_adelicSchwartzAdmittedForms (κ : Type) [Fintype κ] : ev0 (F := F) κ ∈ (adeleClass F).adm κ := by
  have e : ev0 (F := F) κ = GlobalTheory.MixUniq.ev0 κ := LinearMap.ext fun _ => rfl
  rw [e]
  exact GlobalTheory.MixUniq.adelicCoordinatesEvalZeroForm_mem_admissible κ

theorem schr_zero_fst {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (v : κ → AF F) (Ψ : (κ → AF F) → ℂ) :
    schr ψ (0, v) Ψ = fun x => ψ (x ⬝ᵥ v) * Ψ x := by
  funext x
  simp [schr]

theorem siegelSmall_of (hF : SliceFacts) (hAC : AdaptedChar) : SiegelSmall := by
  intro F E _ _ _ _ _ σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' om1 hsp1 hsr1 φ₀ hφ₀ h0 om' hbox
  intro l hl hinv p t hpt φ hφ
  change G2 σ Y at p
  have hψ : IsStd d.B.ψ := d.ok.good.std

  have hchar : ∀ (y : Fin d.m × Fin n × Fin 2 → AF F), ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2),
      l (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = l φ := by
    intro y φ hφ
    obtain ⟨z, hz⟩ := (hAC F E σ d.m n d.bs d.A Y b dd' had' hb).2 y
    have := hinv z φ hφ
    rw [Darboux.rho, hz, schr_zero_fst] at this
    exact this
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.CharInvForm.main F d.B.ψ hψ (Fin d.m × Fin n × Fin 2) l hl hchar

  have hbm : boxFun φ φ₀ ∈ schA F (K1 d.m n) := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ hφ φ₀ hφ₀
  have hb1 := hbox p φ hφ
  have hm1 : boxFun (om' p φ) φ₀ ∈ schA F (K1 d.m n) := hb1 ▸ hsp1.pres (j p) _ hbm
  have hmem : om' p φ ∈ schA F (Fin d.m × Fin n × Fin 2) := by
    have := (hF F _ _).1 _ hm1
    rwa [slice0_box_one _ h0] at this
  change l (om' p φ) = (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
    (((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t))) : ℝ) ^
      ((Fintype.card (Fin d.m) : ℝ) / 2) : ℝ) : ℂ) * l φ
  rw [hc _ hmem, hc _ hφ]

  have hv : om' p φ 0 = ev0 (K1 d.m n) (om1 (j p) (boxFun φ φ₀)) := by
    rw [hb1]
    simp [ev0, boxFun, h0]

  obtain ⟨t', ht', hdet⟩ := jPar d h hb hj p t hpt
  have hkill : ∀ (z : Matrix (Fin d.m) (Fin d.n) (AE F E)), ∀ Ψ ∈ schA F (K1 d.m n),
      ev0 (K1 d.m n) ((GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).rho d.B.ψ
        (z * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))ᵀ) Ψ) = ev0 (K1 d.m n) Ψ := by
    intro z Ψ _
    have h1 := (hAC F E σ d.m d.n d.bs d.A d.Y d.b dd0 had0 d.ok.frame).1 z
    rw [Darboux.rho, GlobalTheory.TowU.reindexD_e, h1]
    simp [ev0, schr]
  have key := hsr1 (ev0 (K1 d.m n)) (evalZero_mem_adelicSchwartzAdmittedForms _) hkill (j p) t' ht' (boxFun φ φ₀) hbm
  rw [hdet] at key
  change ev0 (K1 d.m n) (om1 (j p) (boxFun φ φ₀)) =
    (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
    (((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t))) : ℝ) ^
      ((Fintype.card (Fin d.m) : ℝ) / 2) : ℝ) : ℂ) * ev0 (K1 d.m n) (boxFun φ φ₀) at key
  simp [ev0, boxFun, h0] at key
  rw [hv]
  simpa [ev0, mul_assoc, mul_comm, mul_left_comm] using congrArg (fun z : ℂ => c * z) key

end PositivityTheory.SiegelWeilFormula.Ald

end
end

